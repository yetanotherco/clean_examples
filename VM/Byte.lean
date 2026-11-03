module

public import VM.Basic

@[expose] public section

/-!
# The BYTE table

The 256 byte values as a static lookup channel. A chip that pulls `⟨x⟩` from it learns
`x.val < 256` and nothing else; `guarantees_iff` is the proof, done once, that this guarantee
is exactly membership in the list. How the list is served as a table of the machine is
`pushStatic` in `Ensemble`.
-/

namespace VM

def byteTable : StaticLookupChannel (F p) field where
  name := "BYTE"
  table := List.map (fun n : ℕ => (n : F p)) (List.range 256)
  Guarantees x := x.val < 256
  guarantees_iff := by
    intro x
    simp only [List.mem_map, List.mem_range]
    constructor
    · intro hx
      exact ⟨x.val, hx, ZMod.natCast_zmod_val x⟩
    · rintro ⟨n, hn, rfl⟩
      rw [val_natCast_of_lt_two_pow_40 (by omega)]
      exact hn

abbrev Byte : Channel (F p) field := .fromStatic _ _ byteTable

end VM
