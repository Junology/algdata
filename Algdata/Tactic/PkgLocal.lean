import Lean

/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Package local declarations

In this file, we develop a mechanics to treat package local declarations; i.e. declarations that are used only in the same project.

## Main definition

We define
* `pkg_local (pkg := PackageName)?` attribute, which register a private declaration in a declaration list associated to `PackageName`, and
* `pkg_include (pkg := PackageName)? ident*` command, which imports declarations specified by `decl`s from the declaration list associated to `PackageName` into the current file.
In both cases, the part `(pkg := PackageName)` is optional; if it is not served, `PackageName` is the head of the current module name (i.e. in the module `A.B.C`, ``PackageName = `A``).

## Worlflow

1. Define a private def/theorem with `pkg_local` attribute:

```lean
-- A.Data.List.Basic

@[pkg_local]
private theorem List.foo {α : Type u} (x : List α) : x.length = x.length := rfl
```

2. In other modules in the same project, import the declaration using `pkg_include` command:

```lean
-- A.Data.List.Lemma

-- #print List.foo -- error before `pkg_include`

pkg_include List.foo

#print List.foo
/-
private theorem List.foo.{u} : {α : Type u} → (x : List α) → x.length = x.length := List.foo
-/
```

-/

-- disable auto-binding of unbounded variables
set_option autoImplicit false

open Lean Elab Term Command Meta

/-!
### `PkgLocalDecl`
-/

/-- The data structure that carries major data of package local declarations -/
structure PkgLocalDecl where
  pkgName : Name
  declName : Name
  deriving Inhabited, Repr, BEq, Hashable


/-!
### `pkg_local` attribute
-/

syntax (name := pkg_local) "pkg_local " ("(" &"pkg" " := " ident ")")? : attr

initialize registerTraceClass `pkg_local

/-- The environment extension to track declarations with @[pkg_local] attribute. -/
initialize pkglocalExtension :
    SimpleScopedEnvExtension PkgLocalDecl (HashSet PkgLocalDecl) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt => dt.insert
    initial := {}
  }

private def Lean.Name.head : Name → Name
| .anonymous => .anonymous
| .str .anonymous x => x
| .str child _ => child.head
| .num child _ => child.head

initialize registerBuiltinAttribute {
  name := `pkg_local
  descr := "Attribute for package-local definitions/theorems."
  applicationTime := .afterTypeChecking
  add := fun declName stx kind => do
    let `(attr| pkg_local $[(pkg := $pkgid)]?) := stx
      | throwError "unexted `@[pkg_local]` attribute {stx}"
    let .global := kind | throwError "`@[pkg_local]` can only be used as a global attribute."
    if !(isPrivateName declName) then
      logWarning "`[@pkg_local]` is used on a non-private declaration."
    MetaM.run' do
      dbg_trace "declName : {declName}"
      let moduleName ← getMainModule
      let pkgName := (pkgid.map fun id => (id.getId)).getD moduleName.head
      dbg_trace "pkgName : {pkgName}"
      pkglocalExtension.add {pkgName, declName}
}


/-!
### `pkg_include` command
-/

syntax (name := pkg_include) "pkg_include " ("(" &"pkg" " := " ident ")")? ident,* : command
syntax (name := pkg_include_all) "pkg_include " ("(" &"pkg" " := " ident ")")? " * " : command

@[inline] def getPkgLocalDecls {m : Type → Type} [Monad m] [MonadEnv m] (pkgName : Name) : m (Array PkgLocalDecl) := do
  let declsAll := pkglocalExtension.getState (← getEnv)
  bif pkgName == .anonymous then
    return declsAll.toArray
  else do
    let mut decls : Array PkgLocalDecl := {}
    for d in declsAll do
      if d.pkgName = pkgName then decls := decls.push d
    return decls

/-- Construct `Lean.Declaration` from `PkgLocalDecl` -/
@[inline] def makeDecl {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (pkgdecl : PkgLocalDecl) : m Declaration := do
  let cinfo ← getConstInfo pkgdecl.declName
  let name : Name :=
    mkPrivateName (← getEnv) ((privateToUserName? pkgdecl.declName).getD pkgdecl.declName)
  if (← getEnv).contains name then
    throwError s!"'{name}' has already been declared"
  let constval : ConstantVal := {
    name := name,
    levelParams := cinfo.levelParams,
    type := cinfo.type
  }
  match cinfo with
  | .thmInfo tinfo =>
    return Declaration.thmDecl {
      constval with
      value := mkConst pkgdecl.declName (tinfo.levelParams.map mkLevelParam),
    }
  | _ =>
    return Declaration.defnDecl {
      constval with
      value := mkConst pkgdecl.declName (cinfo.levelParams.map mkLevelParam),
      hints := ReducibilityHints.abbrev,
      safety := if cinfo.isUnsafe then .unsafe else .safe
    }

@[command_elab «pkg_include»]
def elabPkgInclude : CommandElab := fun stx => do
  let `(command| pkg_include $[(pkg := $pkgid)]? $ids,*) := stx
    | throwError "invalid use of 'pkg_include' command: {stx}"
  let pkgName : Name := (pkgid.map fun id => id.getId).getD (← getMainModule).head
  let pkgdecls ← getPkgLocalDecls pkgName
  let mut decls : Array PkgLocalDecl := {}
  for id in ids.getElems do
    dbg_trace "finding {id.getId} from {repr pkgdecls}"
    let some pkgdecl := pkgdecls.find? fun d => id.getId.isSuffixOf d.declName
      | throwError "local declaration not found: {id}"
    dbg_trace "{id} → {repr pkgdecl} found"
    decls := decls.push pkgdecl
  liftCoreM do
    for decl in decls do
      let decl ← makeDecl decl
      addDecl decl
      compileDecl decl

@[command_elab «pkg_include_all»]
def elabPkgIncludeAll : CommandElab := fun stx => do
  let `(command| pkg_include $[(pkg := $pkgid)]? *) := stx
    | throwError "invalid use of 'pkg_include' command: {stx}"
  let pkgdecls := pkglocalExtension.getState (← getEnv)
  liftCoreM do
    for pkgdecl in pkgdecls do
      let decl ← makeDecl pkgdecl
      addDecl decl
      compileDecl decl

