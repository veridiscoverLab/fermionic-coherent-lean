import Fermionic.RankCertificate
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Complete fixed-coefficient reduction of the actual normal-family Gram.
No samples of the parameters are taken: the three coefficients ab, ac, bc
are kept separately, with a common basis and all 120 original directions. -/
namespace Fermionic.RankCertificate

abbrev NormalIndex := Fin 8 ⊕ ((Fin 4 × Fin 24) ⊕ (Fin 4 × Fin 4))

def normalZeroPair : Fin 8 → Pair := ![(0,9),(1,8),(2,11),(3,10),(4,13),(5,12),(6,15),(7,14)]
def normalOffPair : Fin 96 → Pair := ![(0,2),(2,9),(0,11),(9,11),(0,3),(3,9),(0,10),(9,10),(0,4),(4,9),(0,13),(9,13),(0,5),(5,9),(0,12),(9,12),(0,6),(6,9),(0,15),(9,15),(0,7),(7,9),(0,14),(9,14),(1,2),(2,8),(1,11),(8,11),(1,3),(3,8),(1,10),(8,10),(1,4),(4,8),(1,13),(8,13),(1,5),(5,8),(1,12),(8,12),(1,6),(6,8),(1,15),(8,15),(1,7),(7,8),(1,14),(8,14),(2,4),(4,11),(2,13),(11,13),(2,5),(5,11),(2,12),(11,12),(2,6),(6,11),(2,15),(11,15),(2,7),(7,11),(2,14),(11,14),(3,4),(4,10),(3,13),(10,13),(3,5),(5,10),(3,12),(10,12),(3,6),(6,10),(3,15),(10,15),(3,7),(7,10),(3,14),(10,14),(4,6),(6,13),(4,15),(13,15),(4,7),(7,13),(4,14),(13,14),(5,6),(6,12),(5,15),(12,15),(5,7),(7,12),(5,14),(12,14)]
def normalMiddlePair : Fin 16 → Pair := ![(0,1),(0,8),(1,9),(8,9),(2,3),(2,10),(3,11),(10,11),(4,5),(4,12),(5,13),(12,13),(6,7),(6,14),(7,15),(14,15)]
def normalOffSign : Fin 96 → ℤ := ![-1,-1,1,-1,-1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,1,-1,1,1,1,-1,1,-1,-1,-1,1,1,1,-1,1,-1,-1,-1,1,1,1,-1,1,-1,-1,-1,-1,1,-1,-1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,1,-1,1,1,1,-1,1,-1,-1,-1,1,1,1,-1,1,-1,-1,-1,-1,1,-1,-1,-1,-1,1,-1,1,1,1,-1,1,-1,-1]

def normalCoordinatePair : NormalIndex → Pair
  | .inl i => normalZeroPair i
  | .inr (.inl (i,j)) => normalOffPair ⟨4*j.val+i.val, by omega⟩
  | .inr (.inr (i,j)) => normalMiddlePair ⟨4*j.val+i.val, by omega⟩

def normalCoordinateSign : NormalIndex → ℤ
  | .inl _ => 1
  | .inr (.inl (i,j)) => normalOffSign ⟨4*j.val+i.val, by omega⟩
  | .inr (.inr _) => 1

set_option maxRecDepth 100000 in
theorem normal_coordinate_pair_sorted :
    ∀ i : NormalIndex, (normalCoordinatePair i).1 < (normalCoordinatePair i).2 := by
  decide

def normalBasisPair (i : NormalIndex) : {p : Pair // p.1 < p.2} :=
  ⟨normalCoordinatePair i, normal_coordinate_pair_sorted i⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalBasisPair_bijective : Function.Bijective normalBasisPair := by decide

set_option maxRecDepth 100000 in
theorem normalCoordinateSign_square :
    ∀ i : NormalIndex, normalCoordinateSign i * normalCoordinateSign i = 1 := by decide

/-- Coefficients of the actual Gaussian product
(1+e01)(1+e23)(1+e45)(1+e67), on eight-bit occupation masks. -/
def pairedGaussianCoefficient (m : ℕ) : ℤ :=
  if (m.testBit 0 == m.testBit 1) && (m.testBit 2 == m.testBit 3) &&
     (m.testBit 4 == m.testBit 5) && (m.testBit 6 == m.testBit 7)
  then 1 else 0

def topCoefficient (m : ℕ) : ℤ := if m = 255 then 1 else 0

/-- Bilinear Chevalley pairing of J2 applied to one basis term and to the
complete second vector. The inverse mask transform is the same XOR. -/
def fixed_dynamic_pairing (p q : Pair) (u : ℕ) (f : ℕ → ℤ) : ℤ :=
  let out := bivectorOutput p u
  let v := bivectorOutput q (Nat.xor 255 out)
  bivectorCoefficient2 p u * chevalleySign out * bivectorCoefficient2 q v * f v

/-- The coefficients of ab, ac, bc in four times the complete quadratic Gram.
The symmetric second term is essential and is retained for every direction. -/
def normalRawCoefficient (kind : Fin 3) (p q : Pair) : ℤ :=
  let u := if kind = 2 then 255 else 0
  let f := if kind = 0 then topCoefficient else pairedGaussianCoefficient
  dualSign p * (fixed_dynamic_pairing (dualPair p) q u f +
    fixed_dynamic_pairing q (dualPair p) u f)

def normalReindexedCoefficient (kind : Fin 3) (i j : NormalIndex) : ℤ :=
  normalCoordinateSign i * normalCoordinateSign j *
    normalRawCoefficient kind (normalCoordinatePair i) (normalCoordinatePair j)

def normalTInt (x y z : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![x+y+z,z,z,2*z;-y,0,0,-z;-y,0,0,-z;2*y,y,y,x+y+z]

def normalRInt (x y z : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![x+y+z,-3*z,-3*z,-6*z;
     3*y,2*(x+y+z),2*(x+y+z),3*z;
     3*y,2*(x+y+z),2*(x+y+z),3*z;
     -6*y,-3*y,-3*y,x+y+z]

/-- Four times I4 tensor T + ones4 tensor O, with R=T+4O. -/
def normalMiddleInt (x y z : ℤ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ :=
  fun i j => (if i.2 = j.2 then 4 * normalTInt x y z i.1 j.1 else 0) +
    normalRInt x y z i.1 j.1 - normalTInt x y z i.1 j.1

def normalFormInt (x y z : ℤ) : Matrix NormalIndex NormalIndex ℤ :=
  Matrix.fromBlocks (0 : Matrix (Fin 8) (Fin 8) ℤ) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal (fun _ : Fin 24 => 4 • normalTInt x y z))
      0 0 (normalMiddleInt x y z))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_normal_coefficients :
    ∀ kind : Fin 3, ∀ i j : NormalIndex,
      normalReindexedCoefficient kind i j =
        normalFormInt (if kind = 0 then 1 else 0)
          (if kind = 1 then 1 else 0) (if kind = 2 then 1 else 0) i j := by
  decide

end Fermionic.RankCertificate

#print axioms Fermionic.RankCertificate.normalBasisPair_bijective
#print axioms Fermionic.RankCertificate.all_normal_coefficients
