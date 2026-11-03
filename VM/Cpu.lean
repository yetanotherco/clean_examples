module

public import VM.Adder
public import VM.Multiplier

@[expose] public section

/-!
# A consumer of the `ADD` and `MUL` buses

A toy "CPU" row that does no arithmetic. Two selector bits say which operation the row is;
the row pulls the matching message from `ADD` or `MUL`, and that is its whole circuit. A row
with both selectors off is padding: it pulls nothing and promises nothing. The soundness
proof is each bus guarantee, read back under its selector.
-/

namespace VM.Cpu

structure Row (F : Type) where
  is_add : F
  is_mul : F
  a : F
  b : F
  out : F
  out_hi : F
deriving ProvableStruct

def main (r : Var Row (F p)) : Circuit (F p) Unit := do
  isBit r.is_add
  isBit r.is_mul
  assertZero (r.is_add * r.is_mul)
  AddBus.pullIf r.is_add ⟨r.a, r.b, r.out⟩
  MulBus.pullIf r.is_mul ⟨r.a, r.b, r.out, r.out_hi⟩

def Spec (r : Row (F p)) : Prop :=
  (r.is_add = 1 → r.out.val = (r.a.val + r.b.val) % 256) ∧
  (r.is_mul = 1 → r.a.val * r.b.val = r.out.val + 256 * r.out_hi.val)

/-- The row the honest prover fills in: a valid selector pattern, and the result of the
selected operation. -/
def Honest (r : Row (F p)) : Prop :=
  IsBool r.is_add ∧ IsBool r.is_mul ∧ ¬(r.is_add = 1 ∧ r.is_mul = 1) ∧
  (r.is_add = 1 → r.a.val < 256 ∧ r.b.val < 256 ∧ r.out.val = (r.a.val + r.b.val) % 256) ∧
  (r.is_mul = 1 → r.a.val < 256 ∧ r.b.val < 256 ∧
    r.a.val * r.b.val = r.out.val + 256 * r.out_hi.val)

def circuit : GeneralFormalCircuit (F p) Row unit where
  main
  Spec r _ _ := Spec r
  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨is_add, is_mul, a, b, out, out_hi⟩ := input_var
    simp only [circuit_norm, main, isBit, AddBus, MulBus]
    refine ⟨fun _ h => h, fun env ⟨hA, hM, _⟩ => ?_⟩
    rcases mul_one_sub_eq_zero_iff.mp hA with h | h <;>
      rcases mul_one_sub_eq_zero_iff.mp hM with h' | h' <;> simp [h, h']

  soundness := by
    circuit_proof_start [main, isBit, Spec, AddBus, MulBus]
    obtain ⟨hA, hM, _, hadd, hmul⟩ := h_holds
    refine ⟨⟨fun h => (hadd (neg_inj.mpr h)).2.2, fun h => (hmul (neg_inj.mpr h)).2.2⟩, ?_⟩
    rcases mul_one_sub_eq_zero_iff.mp hA with h | h <;>
      rcases mul_one_sub_eq_zero_iff.mp hM with h' | h' <;> simp [h, h']

  ProverAssumptions r _ _ := Honest r

  completeness := by
    circuit_proof_start [main, isBit, AddBus, MulBus, Honest]
    obtain ⟨hA, hM, hAM, hadd, hmul⟩ := h_assumptions
    refine ⟨mul_one_sub_eq_zero_iff.mpr hA, mul_one_sub_eq_zero_iff.mpr hM, ?_,
      fun h => hadd (neg_inj.mp h), fun h => hmul (neg_inj.mp h)⟩
    rcases hA with h | h <;> rcases hM with h' | h' <;> simp_all

end VM.Cpu
