module

public import VM.Byte
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The byte multiplier

One row per product: `a · b = lo + 256 · hi`, a two-limb result. The row pulls "is a byte"
for all four values, constrains the product identity, and pushes the result on the `MUL` bus.
Compared with the adder, the identity is quadratic and the result has two limbs; the shape of
the proof is the same.
-/

namespace VM

/-- A message on the `MUL` bus: two operands and the two limbs of their product. -/
structure MulMsg (F : Type) where
  a : F
  b : F
  lo : F
  hi : F
deriving ProvableStruct

/-- What a puller of the `MUL` bus learns about a message. -/
def MulBus : Channel (F p) MulMsg where
  name := "MUL"
  Guarantees m _ :=
    m.a.val < 256 ∧ m.b.val < 256 ∧ m.a.val * m.b.val = m.lo.val + 256 * m.hi.val

namespace Multiplier

structure Row (F : Type) where
  a : F
  b : F
  lo : F
  hi : F
deriving ProvableStruct

def main (r : Var Row (F p)) : Circuit (F p) Unit := do
  Byte.pull r.a
  Byte.pull r.b
  Byte.pull r.lo
  Byte.pull r.hi
  assertZero (r.a * r.b - r.lo - 256 * r.hi)
  MulBus.push ⟨r.a, r.b, r.lo, r.hi⟩

/-- What a row establishes. -/
def Spec (r : Row (F p)) : Prop := r.a.val * r.b.val = r.lo.val + 256 * r.hi.val

/-- The row the honest prover fills in. -/
def Honest (r : Row (F p)) : Prop :=
  r.a.val < 256 ∧ r.b.val < 256 ∧
  r.lo.val = (r.a.val * r.b.val) % 256 ∧ r.hi.val = (r.a.val * r.b.val) / 256

/-- The product identity, lifted from the field to the naturals: both sides are below `2^16`. -/
lemma lift {a b lo hi : F p} (ha : a.val < 256) (hb : b.val < 256) (hlo : lo.val < 256)
    (hhi : hi.val < 256) (h : a * b - lo - 256 * hi = 0) :
    a.val * b.val = lo.val + 256 * hi.val := by
  have hab : a.val * b.val ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have hcast : ((a.val * b.val : ℕ) : F p) = ((lo.val + 256 * hi.val : ℕ) : F p) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination h
  exact natCast_inj_of_lt (lt_p_of_lt_two_pow_40 (by omega)) (lt_p_of_lt_two_pow_40 (by omega))
    hcast

def circuit : GeneralFormalCircuit (F p) Row unit where
  main
  Spec r _ _ := Spec r
  channelsWithRequirements := [MulBus.toRaw]

  soundness := by
    circuit_proof_start [main, Spec, MulBus, byteTable]
    obtain ⟨ha, hb, hlo, hhi, he⟩ := h_holds
    have hspec := lift ha hb hlo hhi he
    refine ⟨hspec, ?_⟩
    intros
    exact ⟨ha, hb, hspec⟩

  ProverAssumptions r _ _ := Honest r

  completeness := by
    circuit_proof_start [main, MulBus, byteTable, Honest]
    obtain ⟨ha, hb, hlo, hhi⟩ := h_assumptions
    have hab : input_a.val * input_b.val ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨ha, hb, by omega, by omega, ?_⟩
    have h := congrArg (fun n : ℕ => (n : F p))
      (show input_a.val * input_b.val = input_lo.val + 256 * input_hi.val by omega)
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h
    linear_combination h

end Multiplier

end VM
