import tactic
import order.bounded_order
import data.equiv.denumerable

/- In this file we define the basic definitions of the propositional language.
The formulas are parametrized by a type which represents the collection of
propositional variables - this type is required to be denumerable 
(bijective to ℕ), but this is enforced in the theorems not the definition.
We show that if the variables are denumerable then so is the type of formulas.
This is done by an explicit Godel encoding of the formulas' syntactic structure.
-/

/-- Formulas of propositional logic

Form vars ∷= ⦃x : vars⦄ | ⊥ | ~ Form | Form ⋀ Form | Form ⋁ Form -/
inductive Form (vars : Type) : Type
| Bottom : Form
| Var    : vars → Form
| Not    : Form → Form
| And    : Form → Form → Form
| Or     : Form → Form → Form

open Form

-- get the ⊥ notation for Bottom
instance {vars : Type} : has_bot (Form vars) := ⟨Form.Bottom⟩
-- and allow simp to unwrap this definition
@[simp] lemma bottom_eq_bot {vars : Type} : (Form.Bottom : Form vars) = ⊥ := rfl
notation `⦃` a `⦄`  := Form.Var a
notation `~` a     := Form.Not a
notation a ` ⋀ ` b := Form.And a b
notation a ` ⋁ ` b := Form.Or a b

instance {vars : Type} : inhabited (Form vars) := ⟨Form.Bottom⟩

/- Now we show that `Form vars` is denumerable with an explicit bijection, 
given a denumerable `vars`. -/

variables {vars : Type} [denumerable vars]

/- We protect the constructions because they're intended to be used via the
encodable and denumerable typeclass interface, not directly. -/

/-- Bijective encoding of Form into ℕ -/
@[protected]
def enc : Form vars → ℕ
| ⊥       := 0
| ⦃x⦄     := (encodable.encode x) * 4 + 1
| (~ P)   := (enc P) * 4 + 2
| (P ⋀ Q) := (nat.mkpair (enc P) (enc Q)) * 4 + 3
| (P ⋁ Q) := (nat.mkpair (enc P) (enc Q)) * 4 + 4

/-- Bijective decoding of ℕ into Form -/
@[protected]
def dec : ℕ → Form vars
| 0       := ⊥
| (k + 1) :=
  let data := k / 4 in
  -- Proving these allow strong recursion which we need
  have hdata : data < k + 1 := nat.lt_succ_of_le (nat.div_le_self k 4),
  have hfst : data.unpair.fst < k + 1 := lt_of_le_of_lt data.unpair_left_le hdata,
  have hsnd : data.unpair.snd < k + 1 := lt_of_le_of_lt data.unpair_right_le hdata,
  -- the value of k % 4 determines which constructor of Form is encoded
  match k % 4, @nat.mod_lt k 4 dec_trivial with
    | 0, _ := ⦃denumerable.of_nat vars data⦄
    | 1, _ := ~ (dec data)
    | 2, _ := dec (data.unpair.fst) ⋀ dec (data.unpair.snd)
    | 3, _ := dec (data.unpair.fst) ⋁ dec (data.unpair.snd)
    -- k % 4 can't be ≥ 4, but I'm still not sure how dec_trivial works here...
    -- This is based on Mathlib's nat.mod_two_eq_zero_or_one
    | _ + 4, lt_four := absurd lt_four dec_trivial 
  end

/-- Same as Form.dec, but returns the decoded formula wrapped in option.some -/
@[protected]
def dec' : ℕ → option (Form vars) := some ∘ dec

@[protected]
theorem dec_enc_eq : ∀ (A : Form vars), dec (enc A) = A :=
begin
  intro A,
  induction A,
  case Form.Bottom {
    simp [dec, enc],
  },
  case Form.Var {
    simp [dec, enc],
  },
  case Form.Not : A ih {
    simp [enc,  dec],
    -- simplify the argument to dec._match_1 before we can unfold the match
    rw add_comm,
    conv in ((1 + enc A * 4) % 4) {
      rw [nat.add_mul_mod_self_right, @nat.mod_eq_of_lt 1 4 (by norm_num)],
    },
    -- unfold the match
    simp [dec._match_1],
    -- simplify the code number
    simp [nat.add_mul_div_right, @nat.div_eq_of_lt 1 4 (by norm_num)],
    exact ih,
  },
  case Form.And : A B ihA ihB {
    -- similar steps to previous case
    simp [enc, dec],
    rw add_comm,
    conv in ((2 + nat.mkpair (enc A) (enc B) * 4) % 4) {
      rw [nat.add_mul_mod_self_right, @nat.mod_eq_of_lt 2 4 (by norm_num)],
    },
    simp [dec._match_1],
    simp [nat.add_mul_div_right, @nat.div_eq_of_lt 2 4 (by norm_num)],
    exact ⟨ihA, ihB⟩
  },
  case Form.Or : A B ihA ihB {
    -- copy pasted from previous case except 3 instead of 2
    simp [enc, dec],
    rw add_comm,
    conv in ((3 + nat.mkpair (enc A) (enc B) * 4) % 4) {
      rw [nat.add_mul_mod_self_right, @nat.mod_eq_of_lt 3 4 (by norm_num)],
    },
    simp [dec._match_1],
    simp [nat.add_mul_div_right, @nat.div_eq_of_lt 3 4 (by norm_num)],
    exact ⟨ihA, ihB⟩
  },
end

@[protected]
theorem dec'_enc_eq (A : Form vars) : dec' (enc A) = some A :=
begin
  simp [dec'],
  exact dec_enc_eq A
end

instance : encodable (Form vars) := ⟨enc, dec', dec'_enc_eq⟩

@[protected]
theorem enc_dec_eq (n : ℕ) : enc (dec n : Form vars) = n :=
begin
  induction n using nat.case_strong_induction_on with n ih,
  case hz {
    simp [dec, enc],
  },
  case hi {
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3, {
      exact match n % 4, @nat.mod_lt n 4 dec_trivial with
      | 0, _ := by {left, refl}
      | 1, _ := by {right, left, refl}
      | 2, _ := by {right, right, left, refl}
      | 3, _ := by {right, right, right, refl}
      | n + 4, lt_four := absurd lt_four dec_trivial 
      end
    },
    simp [dec] at ⊢ ih,
    rcases this with (h0 | h1 | h2 | h3),
    { -- conv avoids "Motive not type correct" error when rw-ing
      conv in (n % 4) {rw h0}, 
      simp [dec._match_1, enc],
      apply congr_arg nat.succ,
      rw [←nat.add_zero (n / 4 * 4), 
          ←h0, 
          add_comm (n / 4 * 4) (n % 4), 
          nat.mod_add_div' n 4],
    },
    { conv in (n % 4) {rw h1}, 
      simp [dec._match_1, enc],
      rw ih (n / 4) (nat.div_le_self n 4),
      apply congr_arg nat.succ,
      nth_rewrite 2 ←h1,
      rw [add_comm (n / 4 * 4) (n % 4), nat.mod_add_div' n 4]
    },
    {
      conv in (n % 4) {rw h2},
      simp [dec._match_1, enc],
      rw ih _ (trans (nat.unpair_left_le (n / 4)) (nat.div_le_self n 4)),
      rw ih _ (trans (nat.unpair_right_le (n / 4)) (nat.div_le_self n 4)),
      rw nat.mkpair_unpair,
      apply congr_arg nat.succ,
      nth_rewrite 2 ←h2,
      rw [add_comm (n / 4 * 4) (n % 4), nat.mod_add_div' n 4]
    },
    {
      conv in (n % 4) {rw h3},
      simp [dec._match_1, enc],
      rw ih _ (trans (nat.unpair_left_le (n / 4)) (nat.div_le_self n 4)),
      rw ih _ (trans (nat.unpair_right_le (n / 4)) (nat.div_le_self n 4)),
      rw nat.mkpair_unpair,
      apply congr_arg nat.succ,
      nth_rewrite 0 ←h3,
      rw [add_comm (n / 4 * 4) (n % 4), nat.mod_add_div' n 4]
    }
  }
end

@[protected]
theorem enc_decode_inv : ∀ (n : ℕ), 
  ∃ (A : Form vars) (H : A ∈ encodable.decode (Form vars) n), 
  encodable.encode A = n :=
begin
  intro n,
  use dec n,
  simp [encodable.encode, encodable.decode, dec'],
  exact enc_dec_eq n
end

instance : denumerable (Form vars) := ⟨enc_decode_inv⟩

#lint