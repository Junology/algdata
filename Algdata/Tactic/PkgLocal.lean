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
  deriving Inhabited, BEq, Hashable

/-- The environment extension to track declarations with @[pkg_local] attribute. -/
initialize pkglocalExtension :
    SimpleScopedEnvExtension PkgLocalDecl (HashSet PkgLocalDecl) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt => dt.insert
    initial := {}
  }

@[inline] def foldPkgLocalDecls {m : Type → Type} [Monad m] [MonadEnv m] {α : Type} (pkgName : Name) (f : α → PkgLocalDecl → m α) (init : α) : m α := do
  let pkgdecls := pkglocalExtension.getState (← getEnv)
  init |> pkgdecls.foldM fun a d =>
    if pkgName.isPrefixOf d.pkgName then
      f a d
    else
      return a

@[inline] def traversePkgLocalDecls {m : Type → Type} [Monad m] [MonadEnv m] (pkgName : Name) (f : PkgLocalDecl → m Unit) : m Unit := do
  let pkgdecls := pkglocalExtension.getState (← getEnv)
  pkgdecls.forM fun d => do
    if pkgName.isPrefixOf d.pkgName then f d

@[inline] def getPkgLocalDecls {m : Type → Type} [Monad m] [MonadEnv m] (pkgName : Name) : m (Array PkgLocalDecl) := do
  ({} : Array PkgLocalDecl) |> foldPkgLocalDecls pkgName fun arr d =>
    return arr.push d
  /-
  let declsAll := pkglocalExtension.getState (← getEnv)
  let mut decls : Array PkgLocalDecl := {}
  for d in declsAll do
    if pkgName.isPrefixOf d.pkgName then decls := decls.push d
  return decls
  -/


/-!
### `pkg_local` attribute
-/

syntax (name := pkg_local) "pkg_local " ("(" &"pkg" " := " ident ")")? : attr

initialize registerTraceClass `pkg_local

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
      let pkgName := (pkgid.map fun id => (id.getId)).getD (←getMainModule).head
      logInfo s!"register the declaration '{declName}' to '{pkgName}'"
      pkglocalExtension.add {pkgName, declName}
}


/-!
### `pkg_include` command
-/

syntax (name := pkg_include) "pkg_include " ("(" &"pkg" " := " ident ")")? ident,* : command
syntax (name := pkg_include_all) "pkg_include " ("(" &"pkg" " := " ident ")")? " * " : command

/-- Construct `Lean.Declaration` from `PkgLocalDecl` -/
@[inline] def makeDecl {m : Type → Type} [Monad m] [MonadEnv m] (pkgdecl : PkgLocalDecl) : m (Option (Name × Declaration)) := do
  let some cinfo := (← getEnv).find? pkgdecl.declName
    | return none
  let name : Name :=
    mkPrivateName (← getEnv) ((privateToUserName? pkgdecl.declName).getD pkgdecl.declName)
  let constval : ConstantVal := {
    name := name,
    levelParams := cinfo.levelParams,
    type := cinfo.type
  }
  match cinfo with
  | .thmInfo tinfo =>
    return .some $ .mk name $ Declaration.thmDecl {
      constval with
      value := mkConst pkgdecl.declName (tinfo.levelParams.map mkLevelParam),
    }
  | _ =>
    return .some $ .mk name $ Declaration.defnDecl {
      constval with
      value := mkConst pkgdecl.declName (cinfo.levelParams.map mkLevelParam),
      hints := ReducibilityHints.abbrev,
      safety := if cinfo.isUnsafe then .unsafe else .safe
    }

@[inline] def runDecl (pkgdecl : PkgLocalDecl) : CoreM Unit := do
  let some (name, decl) ← makeDecl pkgdecl
    | throwError "The environment does not contain '{pkgdecl.declName}'"
  if (← getEnv).contains name then
    throwError "'{name}' has already been declared"
  if let some uname := privateToUserName? name then
    if (← getEnv).contains uname then
      logWarning s!"The constant '{Lean.mkConst uname}' may become ambiguous"
  addDecl decl
  compileDecl decl

@[command_elab «pkg_include»]
def elabPkgInclude : CommandElab := fun stx => do
  let `(command| pkg_include $[(pkg := $pkgid)]? $ids,*) := stx
    | throwError "invalid use of 'pkg_include' command: {stx}"
  let pkgName : Name := (pkgid.map TSyntax.getId).getD (← getMainModule).head
  logInfo s!"include package local declarations from '{pkgName}'"
  let pkgdecls ← getPkgLocalDecls pkgName
  let mut decls : Array PkgLocalDecl := {}
  for id in ids.getElems do
    let some pkgdecl := pkgdecls.find? fun d => id.getId.isSuffixOf d.declName
      | throwError "local declaration not found: {id}"
    decls := decls.push pkgdecl
  liftCoreM <| decls.forM runDecl

@[command_elab «pkg_include_all»]
def elabPkgIncludeAll : CommandElab := fun stx => do
  let `(command| pkg_include $[(pkg := $pkgid)]? *) := stx
    | throwError "invalid use of 'pkg_include' command: {stx}"
  let pkgName := (pkgid.map TSyntax.getId).getD (← getMainModule).head
  logInfo s!"include package local declarations from '{pkgName}'"
  liftCoreM <|
    traversePkgLocalDecls pkgName runDecl


/-!
### `#pkg_list` command
-/

syntax (name := pkg_list) "#pkg_list " ("(" &"pkg" " := " ident ")")? : command

@[command_elab «pkg_list»]
def elabPkgList : CommandElab := fun stx => do
  let `(command| #pkg_list $[(pkg := $pkgid)]?) := stx
    | throwError "invalid use of '#pkg_list' command: {stx}"
  let pkgName := (pkgid.map TSyntax.getId).getD (← getMainModule).head
  let msg ←
    f!"package '{pkgName}' has the following local declarations:" |>
      foldPkgLocalDecls pkgName fun msg d => do
        match (← getEnv).find? d.declName with
        | some (.axiomInfo ainfo) =>
          return msg ++ Std.Format.indentD f!"axiom {Lean.mkConst ainfo.name (ainfo.levelParams.map mkLevelParam)} : {ainfo.type}"
        | some (.defnInfo dinfo) =>
          return msg ++ Std.Format.indentD f!"def {Lean.mkConst dinfo.name (dinfo.levelParams.map mkLevelParam)} : {dinfo.type}"
        | some (.thmInfo tinfo) =>
          return msg ++ Std.Format.indentD f!"theorem {Lean.mkConst tinfo.name (tinfo.levelParams.map mkLevelParam)} : {tinfo.type}"
        | some (.opaqueInfo oinfo) =>
          return msg ++ Std.Format.indentD f!"opaque {Lean.mkConst oinfo.name (oinfo.levelParams.map mkLevelParam)} : {oinfo.type}"
        | some _ =>
          logWarning s!"'{d.declName}' is an internal declaration"
          return msg
        | none =>
          logWarning s!"The environment does not contain '{d.declName}'"
          return msg
  logInfo msg.pretty
