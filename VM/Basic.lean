module

public import Clean.Circuit
public import CompPoly.Fields.Goldilocks

@[expose] public section

/-!
# The field and a few lemmas

Goldilocks, `2^64 - 2^32 + 1`, and the facts every proof uses: a field identity between small
naturals lifts to the naturals, and `x · (1 − x) = 0` means `x` is a bit.
-/

namespace VM

abbrev p : ℕ := Goldilocks.fieldSize

instance : Fact p.Prime := ⟨Goldilocks.is_prime⟩

lemma lt_p_of_lt_two_pow_40 {n : ℕ} (h : n < 2^40) : n < p := lt_trans h (by decide)

lemma val_natCast_of_lt_two_pow_40 {n : ℕ} (h : n < 2^40) : ((n : F p)).val = n :=
  ZMod.val_natCast_of_lt (lt_p_of_lt_two_pow_40 h)

/-- Casting naturals below `p` into the field is injective. -/
lemma natCast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : F p) = (b : F p)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

/-- Clean's `IsBool.iff_mul_sub_one`, in the orientation the constraint is written in. -/
lemma mul_one_sub_eq_zero_iff {x : F p} : x * (1 - x) = 0 ↔ IsBool x := by
  rw [IsBool.iff_mul_sub_one, ← neg_sub x 1, mul_neg, neg_eq_zero]

lemma isBool_of_val_lt_two {x : F p} (h : x.val < 2) : IsBool x := by
  have hx : x = (x.val : F p) := (ZMod.natCast_zmod_val x).symm
  rcases Nat.lt_succ_iff.mp h |>.lt_or_eq with h0 | h1
  · left; rw [hx, Nat.lt_one_iff.mp h0]; simp
  · right; rw [hx, h1]; simp

/-- `x` is a bit: `x · (1 − x) = 0`. -/
@[circuit_norm]
def isBit (x : Expression (F p)) : Circuit (F p) Unit :=
  assertZero (x * (1 - x))

-- Circuit inference does not unfold user wrappers; bridge it to its body.
instance (x : Expression (F p)) : ExplicitCircuit (isBit x) :=
  .of_eq (circuit' := assertZero (x * (1 - x))) rfl (by infer_explicit_circuit)

end VM
