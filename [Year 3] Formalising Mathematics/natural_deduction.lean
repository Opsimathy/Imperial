import formula

variable {vars : Type}

/- The soundness and completeness theorems are always proven with respect to a 
particular proof system. In this file we define the natural deduction proof 
system as an inductive type and prove the syntactic compactness theorem.
-/

/-- Gentzen-style (Proof Tree) Natural Deduction -/
inductive Deriv : set (Form vars) → Form vars → Prop
| Bottom_E  : ∀ {Γ : set (Form vars)} {A : Form vars},
              Deriv Γ ⊥ → Deriv Γ A
| Ax        : ∀ {Γ : set (Form vars)} {A : Form vars},
              A ∈ Γ → Deriv Γ A
| Not_I     : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv (insert A Γ) ⊥ → Deriv Γ (~ A)
| Not_E     : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv Γ (~ A) → Deriv Γ A → Deriv Γ ⊥
| And_I     : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ B → Deriv Γ (A ⋀ B)
| And_E_1   : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ A
| And_E_2   : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ B
| Or_I_1    : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ (A ⋁ B)
| Or_I_2    : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ B → Deriv Γ (A ⋁ B)
| Or_E      : ∀ {Γ : set (Form vars)} {A B C : Form vars}, 
              Deriv Γ (A ⋁ B) → Deriv (insert A Γ) C → Deriv (insert B Γ) C 
              → Deriv Γ C
| Contra    : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv (insert (~ A) Γ) ⊥ → Deriv Γ A
-- This is an admissible rule (we can prove it from the others), but its easier
-- to just add it as most of the inductive cases are easy to prove for this rule
-- and its helpful in many situations.
| Weakening : ∀ {Γ Δ : set (Form vars)} {A : Form vars},
              (Γ ⊆ Δ) → (Deriv Γ A) → (Deriv Δ A)

open Deriv

notation Γ ` ⊩ ` A := Deriv Γ A
notation Γ ` ⊮ ` A := ¬ Deriv Γ A

/-- Γ is consistent if it cannnot derive ⊥.-/
def consistent   (Γ : set (Form vars)) : Prop := Γ ⊮ ⊥
/-- Γ is inconsistent if it can derive ⊥.-/
def inconsistent (Γ : set (Form vars)) : Prop := Γ ⊩ ⊥ 

/-- An example derivation:
(Ax) ---------  --------- (Ax)
     A, B ⊩ A   A, B ⊩ B
    --------------------- (⋀I)
         A, B ⊩ A ⋀ B
-/
example {A B : Form vars} : {A, B} ⊩ (A ⋀ B) :=
begin
  apply Deriv.And_I,
  {
    apply Deriv.Ax,
    simp,
  },
  {
    apply Deriv.Ax,
    simp
  }
end

/-- The following syntactic compactness theorem states that if Γ ⊩ A,
then A can be derived from a finite subset of Γ. This is intuitively obvious
because a derivation is a finite structure so it must only use finitely many
assumptions from Γ because there can only be finite occurences of the Ax rule.
Regardless we have to construct such a finite subset explicitly for a formal
proof. -/
theorem deriv_compactness
{Γ : set (Form vars)} {A} (h : Γ ⊩ A) 
  : ∃ Δ, Δ ⊆ Γ ∧ Δ.finite ∧ (Δ ⊩ A) :=
begin
  induction h,
  -- the proof inductively constructs a Δ containing only the assumptions that
  -- are actually used in the derivation. Most cases are trivial because we can
  -- just use the same set given by the IH. The exception are rules Not_I, Or_E 
  -- and Contra where the premise(s) add new assumptions. For these rules, we 
  -- have to remove the added assumptions from the set given in the ih and
  -- prove that this new set satisfies the requirements.
  case Deriv.Bottom_E : Γ A _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hbot⟩,
    use Δ, use hsub, use hfin,
    use Deriv.Bottom_E hbot,
  },
  case Deriv.Ax : Γ A h {
    refine ⟨{A}, _, _, _⟩,
    { simp, use h },
    { simp },
    { apply Deriv.Ax, simp }
  },
  case Deriv.Not_I : Γ A _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hbot⟩,
    use Δ \ {A}, -- remove the assumption added by the Not_I rule
    refine ⟨_, _, _⟩,
    { simp, exact hsub },
    { exact set.finite.subset hfin (set.diff_subset Δ {A}) },
    { apply Deriv.Not_I, simp, exact Deriv.Weakening (by simp : Δ ⊆ insert A Δ) hbot }
  },
  case Deriv.Not_E : Γ A _ _ ihnA ihA {
    rcases ihnA with ⟨ΓnA, hnAsub, hnAfin, hnA⟩,
    rcases ihA with ⟨ΓA, hAsub, hAfin, hA⟩,
    refine ⟨ΓnA ∪ ΓA, _, _, _⟩,
    { simp [hnAsub, hAsub] },
    { simp [hnAfin, hAfin] },
    { apply Deriv.Not_E,
      exact Deriv.Weakening (by simp) hnA,
      exact Deriv.Weakening (by simp) hA },
  },
  case Deriv.And_I : Γ A B _ _ ihA ihB {
    rcases ihA with ⟨ΓA, hAsub, hAfin, hA⟩,
    rcases ihB with ⟨ΓB, hBsub, hBfin, hB⟩,
    refine ⟨ΓA ∪ ΓB, _, _, _⟩,
    { simp [hAsub, hBsub] },
    { simp [hAfin, hBfin] },
    { apply Deriv.And_I,
      exact Deriv.Weakening (by simp) hA,
      exact Deriv.Weakening (by simp) hB },
  },
  case Deriv.And_E_1 : Γ A B _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hA⟩,
    exact ⟨Δ, hsub, hfin, Deriv.And_E_1 hA⟩
  },
  case Deriv.And_E_2 : Γ A B _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hB⟩,
    exact ⟨Δ, hsub, hfin, Deriv.And_E_2 hB⟩
  },
  case Deriv.Or_I_1 : Γ A B _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hA⟩,
    exact ⟨Δ, hsub, hfin, Deriv.Or_I_1 hA⟩
  },
  case Deriv.Or_I_2 : Γ A B _ ih {
    rcases ih with ⟨Δ, hsub, hfin, hB⟩,
    exact ⟨Δ, hsub, hfin, Deriv.Or_I_2 hB⟩
  },
  case Deriv.Or_E : Γ A B C _ _ _ ihAB ihAC ihBC {
    rcases ihAB with ⟨ΓAB, hABsub, hABfin, hAB⟩,
    rcases ihAC with ⟨ΓAC, hACsub, hACfin, hAC⟩,
    rcases ihBC with ⟨ΓBC, hBCsub, hBCfin, hBC⟩,
    -- all the assumptions used except for the ones added by the Or_E rule.
    use ΓAB ∪ ((ΓAC \ {A}) ∪ (ΓBC \ {B})),
    refine ⟨_, _, _⟩,
    { simp, exact ⟨hABsub, hACsub, hBCsub⟩ },
    { simp,
      exact ⟨hABfin, 
             set.finite.subset hACfin (set.diff_subset ΓAC {A}), 
             set.finite.subset hBCfin (set.diff_subset ΓBC {B})⟩ },
    { apply Deriv.Or_E,
      { exact Deriv.Weakening (set.subset_union_left _ _) hAB },
      { rw [←set.union_insert, ←set.insert_union, set.insert_diff_singleton],
        refine Deriv.Weakening _ hAC,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_of_subset_left,
        exact set.subset_insert A ΓAC },
      { rw [←set.union_insert, ←set.union_insert, set.insert_diff_singleton],
        refine Deriv.Weakening _ hBC,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_of_subset_right,
        exact set.subset_insert B ΓBC }
    }
  },
  case Deriv.Contra : Γ A _ ih {
    -- this case is similar to Not_I
    rcases ih with ⟨Δ, hsub, hfin, hbot⟩,
    use Δ \ {~ A},
    refine ⟨_, _, _⟩,
    { simp, exact hsub },
    { exact set.finite.subset hfin (set.diff_subset Δ {~ A}) },
    { apply Deriv.Contra, 
      simp, 
      exact Deriv.Weakening (by simp : Δ ⊆ insert (~ A) Δ) hbot }
  },
  case Deriv.Weakening : Γ SΓ A hsub _ ih {
    rcases ih with ⟨Δ, hsub', hfin, hA⟩,
    exact ⟨Δ, trans hsub' hsub, hfin, hA⟩
  }
end

/-- An alternative statement of the compactness theorem. -/
theorem deriv_compactness' {Γ : set (Form vars)} 
  (hfincon : ∀ (Δ : set (Form vars)), Δ ⊆ Γ → Δ.finite → consistent Δ) 
  : consistent Γ :=
begin
  -- this is just contrapositive of deriv_compactness
  have := mt deriv_compactness,
  simp at this,
  exact this hfincon,
end

#lint