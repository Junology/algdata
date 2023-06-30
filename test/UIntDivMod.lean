import Algdata.Classes.UInt
import Algdata.Algebra.UIntAdic2.Basic

open UIntAdic2

#eval Array.map (λ n => recip n * n) $ Array.ofFn (λ (i : Fin 128) => UIntAdic2.ofNat (α:=UInt8) (i.1 * 2 + 1))

def testarr : Array (UIntAdic2 UInt8 × UIntAdic2 UInt8) :=
  Array.ofFn (n:=1024) (λ i => (UIntAdic2.ofNat (i.1 / 32), UIntAdic2.ofNat (i.1 % 32)))

#eval Array.map (λ (n, m) => n == (n/m)*m + n%m) testarr

