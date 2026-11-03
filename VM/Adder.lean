module

public import VM.Byte
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The byte adder

One row per addition: `a + b = sum (mod 256)`, with the overflow in `carry`. The row pulls
"is a byte" for its three values, constrains the carry to be a bit, and pushes the result on
the `ADD` bus, where a consumer can pick it up.
-/

namespace VM

/-- A message on the `ADD` bus: two operands and their sum. -/
structure AddMsg (F : Type) where
  a : F
  b : F
  sum : F
deriving ProvableStruct

/-- What a puller of the `ADD` bus learns about a message. -/
def AddBus : Channel (F p) AddMsg where
  name := "ADD"
  Guarantees m _ := m.a.val < 256 ∧ m.b.val < 256 ∧ m.sum.val = (m.a.val + m.b.val) % 256

namespace Adder

structure Row (F : Type) where
  a : F
  b : F
  sum : F
  carry : F
deriving ProvableStruct

def main (r : Var Row (F p)) : Circuit (F p) Unit := do
  Byte.pull r.a
  Byte.pull r.b
  Byte.pull r.sum
  isBit r.carry
  assertZero (r.a + r.b - r.sum - 256 * r.carry)
  AddBus.push ⟨r.a, r.b, r.sum⟩

/-- What a row establishes. -/
def Spec (r : Row (F p)) : Prop := r.sum.val = (r.a.val + r.b.val) % 256

/-- The row the honest prover fills in. -/
def Honest (r : Row (F p)) : Prop :=
  r.a.val < 256 ∧ r.b.val < 256 ∧ r.sum.val = (r.a.val + r.b.val) % 256 ∧
  r.carry.val = (r.a.val + r.b.val) / 256

/-- The addition identity, lifted from the field to the naturals: every term is small. -/
lemma lift {a b sum carry : F p} (ha : a.val < 256) (hb : b.val < 256) (hs : sum.val < 256)
    (hc : IsBool carry) (h : a + b - sum - 256 * carry = 0) :
    a.val + b.val = sum.val + 256 * carry.val := by
  have hc2 := IsBool.val_lt_two hc
  have hcast : ((a.val + b.val : ℕ) : F p) = ((sum.val + 256 * carry.val : ℕ) : F p) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination h
  exact natCast_inj_of_lt (lt_p_of_lt_two_pow_40 (by omega)) (lt_p_of_lt_two_pow_40 (by omega))
    hcast

def circuit : GeneralFormalCircuit (F p) Row unit where
  main
  Spec r _ _ := Spec r
  channelsWithRequirements := [AddBus.toRaw]

  soundness := by
    circuit_proof_start [main, isBit, Spec, AddBus, byteTable]
    obtain ⟨ha, hb, hs, hc, he⟩ := h_holds
    have e := lift ha hb hs (mul_one_sub_eq_zero_iff.mp hc) he
    have hspec : input_sum.val = (input_a.val + input_b.val) % 256 := by omega
    refine ⟨hspec, ?_⟩
    intros
    exact ⟨ha, hb, hspec⟩

  ProverAssumptions r _ _ := Honest r

  completeness := by
    circuit_proof_start [main, isBit, AddBus, byteTable, Honest]
    obtain ⟨ha, hb, hs, hc⟩ := h_assumptions
    refine ⟨ha, hb, by omega, ?_, ?_⟩
    · exact mul_one_sub_eq_zero_iff.mpr (isBool_of_val_lt_two (by omega))
    · have h := congrArg (fun n : ℕ => (n : F p))
        (show input_a.val + input_b.val = input_sum.val + 256 * input_carry.val by omega)
      push_cast at h
      simp only [ZMod.natCast_zmod_val] at h
      linear_combination h

end Adder

end VM
