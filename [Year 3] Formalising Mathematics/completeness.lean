
import natural_deduction
import semantics

variables {vars : Type} {Γ : set (Form vars)} {A B C : Form vars}

/-- A complete set of formulas contains, for every formula A, either A 
or its negation.

Note: this is a different use of the word from the "completeness theorem",
which pertains to the derivation and semantic system, not to sets.
-/
def complete (Γ : set (Form vars)) : Prop := 
  ∀ (A : Form vars), A ∈ Γ ∨ (~ A) ∈ Γ

/-- Let Γ be a set of formulas (we will also require Γ be consistent but this 
is asserted in the corresponding theorem lindenbaum_fn_consistent and 
lindenbaum_lemma).

Using the denumeration A₀, A₁, ... of all formulas, define the following sequence
of sets inductively:

 Γ₀ = Γ

 Γₙ₊₁ = if consistent (insert Aₙ Γₙ) then insert Aₙ Γₙ else insert (~ Aₙ) Γₙ
-/
def lindenbaum_fn (Γ : set (Form vars)) [denumerable vars]
  [∀ (Γ : set (Form vars)), decidable (consistent Γ)] : ℕ → set (Form vars)
| 0 := Γ
| (n + 1) := 
let Aₙ := denumerable.of_nat (Form vars) n in
if consistent (insert Aₙ (lindenbaum_fn n)) 
then insert Aₙ (lindenbaum_fn n) 
else insert (~ Aₙ) (lindenbaum_fn n)

/-- Each of the Γₙ defined above are consistent if the source set Γ is consistent -/
lemma lindenbaum_fn_consistent {Γ : set (Form vars)} {hcon : consistent Γ}
  [denumerable vars] [∀ (Γ : set (Form vars)), decidable (consistent Γ)]
  : ∀ n, consistent (lindenbaum_fn Γ n) :=
begin
  intro n,
  induction n,
  -- Γ₀ = Γ is consistent by assumption
  case nat.zero { exact hcon },
  case nat.succ : k ih {
    simp [lindenbaum_fn, apply_ite consistent],
    set A  := denumerable.of_nat (Form vars) k,
    set Γₖ := lindenbaum_fn Γ k,
    by_cases hc : consistent (insert A Γₖ),
    -- if inserting A is consistent, then the goal immediately follows.
    { rw if_pos hc, exact hc },
    -- if inserting A is inconsistent, then we prove by contradiction since if
    -- inserting A or ~ A are both inconsistent, then we can show it is 
    -- already inconsistent before insertion, thus contradicting the ih.
    { rw if_neg hc, by_contra hnc, simp [consistent] at hc hnc, 
      exact ih (Deriv.Not_E (Deriv.Not_I hnc) (Deriv.Not_I hc)),
    }
  }
end

/-- If i ≤ n, then Γᵢ ⊆ Γₙ, i.e. latter Γs contain all the previous ones. -/
lemma lindenbaum_fn_chain {Γ : set (Form vars)} {n i : ℕ} (hi : i ≤ n)
  [denumerable vars] [∀ (Γ : set (Form vars)), decidable (consistent Γ)] 
  : lindenbaum_fn Γ i ⊆ lindenbaum_fn Γ n :=
begin
  cases lt_or_eq_of_le hi with hlt heq,
  -- if i = n then its trivial
  swap, { rw heq },
  -- otherwise induction
  clear hi,
  induction n,
  -- if n = 0 then there's no i < 0 so vacuously true
  case nat.zero { simp at hlt, exfalso, exact hlt },
  -- for the inductive case
  case nat.succ : k ih { 
    simp [lindenbaum_fn], 
    set A := denumerable.of_nat (Form vars) k,
    split_ifs with hc,
    { cases lt_or_eq_of_le (nat.le_of_lt_succ hlt) with hlt heq,
      -- if (hlt : i < k) then by the ih Γᵢ ⊆ Γₖ and Γₖ ⊆ Γₖ₊₁
      {exact trans (ih hlt) (set.subset_insert A _) },
      -- otherwise (heq : i = k) so Γᵢ = Γₖ and Γₖ ⊆ Γₖ₊₁
      { rw heq, exact set.subset_insert A _ }
    },
    { -- exact same proof as above since we don't care about what formula is being inserted
      cases lt_or_eq_of_le (nat.le_of_lt_succ hlt) with hlt heq,
      -- if (hlt : i < k) then by the ih Γᵢ ⊆ Γₖ and Γₖ ⊆ Γₖ₊₁
      { exact trans (ih hlt) (set.subset_insert (~ A) _) },
      -- otherwise (heq : i = k) so Γᵢ = Γₖ and Γₖ ⊆ Γₖ₊₁
      { rw heq, exact set.subset_insert (~ A) _ }
    }
  }
end

/-- We show that we can take union of all the Γᵢ defined above to form a 
completion of Γ that preserves Γ's consistency. -/
lemma lindenbaum_lemma (Γ : set (Form vars)) (hcon : consistent Γ) 
  [denumerable vars] [∀ (Γ : set (Form vars)), decidable (consistent Γ)]
  : ∃ CΓ, Γ ⊆ CΓ ∧ complete CΓ ∧ consistent CΓ :=
begin
  let CΓ := ⋃ (i : ℕ), (lindenbaum_fn Γ i),
  refine ⟨CΓ, _, _, _⟩,
  -- Γ ⊆ CΓ
  { exact set.subset_Union (lindenbaum_fn Γ) 0 },
  -- complete CΓ
  { rw complete, 
    intro A,
    simp,
    -- if A appears as the nth formula, then it is inserted in Γₙ₊₁ 
    have hA : A ∈ lindenbaum_fn Γ (encodable.encode A + 1) ∨
       (~ A) ∈ lindenbaum_fn Γ (encodable.encode A + 1), {
      simp [lindenbaum_fn],
      split_ifs with hc,
      { left, exact set.mem_insert A _ },
      { right, exact set.mem_insert (~A) _ },
    },
    cases hA,
    { left,
      use encodable.encode A + 1,
      exact hA },
    { right,
      use encodable.encode A + 1,
      exact hA }
  },
  -- consistent CΓ
  { -- First we show that every finite subset of CΓ is a subset of Γₙ for some n
    have hfinsub : ∀ (Δ : set (Form vars)), Δ.finite → Δ ⊆ CΓ → ∃n, Δ ⊆ lindenbaum_fn Γ n, {
      intros Δ hΔfin hsub,
      by_cases hne : Δ.nonempty,
      { -- Suppose Δ is nonempty.
        -- Because Δ is finite, it is a subset of the union of a finite amount of
        -- the Γᵢs in CΓ. We want to take the max of the indices i, as the Γₙ with the greatest
        -- index contains all the other Γᵢs - and so contains Δ.
        have := set.finite_subset_Union hΔfin hsub,
        -- finΓ is the set of indices n - it is finite and defines a subset of CΓ that contains Δ
        rcases this with ⟨finΓ, ⟨hfinΓ⟩, hsubfinΓ⟩,
        haveI := hfinΓ, -- to allow the fintype typeclass to be resolved implicitly
        -- Since Δ is non-empty, finΓ is nonempty, so the maximum over finΓ is defined.
        have hfinΓne : finΓ.to_finset.nonempty, {
          cases hne with A hA,
          specialize hsubfinΓ hA,
          simp at hsubfinΓ,
          rcases hsubfinΓ with ⟨i, hi, _⟩,
          use i,
          rwa set.mem_to_finset,
        },
        use finΓ.to_finset.max' hfinΓne,
        set max_i := finΓ.to_finset.max' hfinΓne,
        -- Now we reason about each δ ∈ Δ from the fact that it belongs to some Γᵢ
        -- where i belongs in finΓ.
        intros δ hδ,
        specialize hsubfinΓ hδ, simp at hsubfinΓ,
        rcases hsubfinΓ with ⟨i, hi, hmemΓi⟩,
        -- using lindenbaum_fn_chain we can show each δ belongs to Γ_max_i 
        apply lindenbaum_fn_chain,
        exact finset.le_max' (finΓ.to_finset) i 
                             (set.mem_to_finset.mpr hi),
        exact hmemΓi
      },
      -- otherwise if Δ is empty, its trivially a subset of any set
      -- so we can pick any Γₙ - let's pick Γ₀ for simplicity.
      { use 0, simp [set.not_nonempty_iff_eq_empty] at hne, rw hne, simp},
    },
    -- every finite subset of CΓ is consistent, since it is a subset of some Γₙ
    -- and those are all consistent.
    have hfincon : ∀ (Δ : set (Form vars)), Δ ⊆ CΓ → Δ.finite → consistent Δ, {
      intros Δ hsub hΔfin,
      rcases hfinsub Δ hΔfin hsub with ⟨n, hsubΓn⟩,
      apply mt (Deriv.Weakening hsubΓn),
      apply lindenbaum_fn_consistent n, exact hcon -- why can't it resolve hcon implicitly???
    },
    -- 
    exact deriv_compactness' hfincon,
  }
end

/-- From the Lindenbaum completion, we can build a semantic model 
(variable assignment) of propositional logic. -/
def lindenbaum_model (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  : vars → bool :=
λ p, if ⦃p⦄ ∈ CΓ then true else false

lemma contradiction_of_deriv_of_nmem 
  (hcomp : complete Γ) (hcon : consistent Γ) 
  : (Γ ⊩ A) →  A ∉ Γ → false :=
begin
  intros hdA hAnin,
  have : (~ A) ∈ Γ := (or_iff_right hAnin).mp (hcomp A),
  have hdnA : (Γ ⊩ ~ A) := Deriv.Ax this,
  have hincon : inconsistent Γ := Deriv.Not_E hdnA hdA,
  exact hcon hincon
end

lemma deriv_iff_mem
  (hcomp : complete Γ) (hcon : consistent Γ) : (Γ ⊩ A) ↔ A ∈ Γ :=
begin
  split,
  { intro hdA,
    by_contra hAnin,
    exact contradiction_of_deriv_of_nmem hcomp hcon hdA hAnin
  },
  { exact Deriv.Ax }
end

/-- We can now show that this new model reflects membership in the completion. -/
lemma truth_lemma
  (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  (hcomp : complete CΓ) (hcon : consistent CΓ)
  : ↥(lindenbaum_model CΓ ⊨ A) ↔ A ∈ CΓ :=
begin
  induction A,
  case Form.Bottom {
    simp [eval],
    rw ←deriv_iff_mem hcomp hcon,
    exact hcon
  },
  case Form.Var {
    simp [eval, lindenbaum_model],
    split_ifs,
    {simp, exact h},
    {simp, exact h}
  },
  case Form.Not : A ih {
    simp [eval, ih],
    split,
    { intro h, exact (or_iff_right h).mp (hcomp A) },
    {
      intro hnA, 
      by_contra hA,
      have hincon : inconsistent CΓ := Deriv.Not_E (Deriv.Ax hnA) (Deriv.Ax hA),
      exact hcon hincon
    },
  },
  case Form.And : A B ihA ihB {
    simp [eval, ihA, ihB],
    split,
    { rintro ⟨hA, hB⟩,
      have hdAB : (CΓ ⊩ (A ⋀ B)) := Deriv.And_I (Deriv.Ax hA) (Deriv.Ax hB),
      by_contra hABnin,
      exact contradiction_of_deriv_of_nmem hcomp hcon hdAB hABnin
    },
    { intro hAB,
      have hdA : (CΓ ⊩ A) := Deriv.And_E_1 (Deriv.Ax hAB),
      have hdB : (CΓ ⊩ B) := Deriv.And_E_2 (Deriv.Ax hAB),
      split,
      {by_contra hAnin, exact contradiction_of_deriv_of_nmem hcomp hcon hdA hAnin},
      {by_contra hBnin, exact contradiction_of_deriv_of_nmem hcomp hcon hdB hBnin}
    },
  },
  case Form.Or : A B ihA ihB {
    simp[eval, ihA, ihB],
    split,
    { intro h,
      rw ←deriv_iff_mem hcomp hcon,
      cases h with hA hB,
      { exact Deriv.Or_I_1 (Deriv.Ax hA) },
      { exact Deriv.Or_I_2 (Deriv.Ax hB) }
    },
    { intro hAB,
      by_contra h,
      rw [not_or_distrib] at h,
      cases h with hAnin hBnin,
      have hnAin : (~ A) ∈ CΓ := (or_iff_right hAnin).mp (hcomp A),
      have hnBin : (~ B) ∈ CΓ := (or_iff_right hBnin).mp (hcomp B),
      /- Build the derivation:
                    (Ax)------------ (Ax)----------   (Ax)----------- (Ax)----------
                        CΓ, A ⊩ ~ A      CΓ, A ⊩ A       CΓ, B ⊩ ~ B     CΓ, B ⊩ B
    (Ax)----------- (~E)---------------------------   (~E)--------------------------
        CΓ ⊩ A ⋁ B             CΓ, A ⊩ ⊥                        CΓ, B ⊩ ⊥ 
        ---------------------------------------------------------------------------
                                      CΓ ⊩ ⊥
      -/
      have hincon : (inconsistent CΓ), {
        apply Deriv.Or_E,
        { exact Deriv.Ax hAB },
        { apply Deriv.Not_E, 
          exact Deriv.Ax (or.intro_right _ hnAin),
          exact Deriv.Ax (or.intro_left _ rfl)},
        { apply Deriv.Not_E, 
          exact Deriv.Ax (or.intro_right _ hnBin),
          exact Deriv.Ax (or.intro_left _ rfl)
        }
      },
      exact hcon hincon
    }
  },
end

theorem completeness' {Γ : set (Form vars)} [denumerable vars]
  : consistent Γ → satisfiable Γ := 
begin
  -- specifically, we need membership in CΓ to be decidable
  -- and consistency of sets of formulas to be decicable
  -- hence we use classical reasoning
  classical,
  intro hcon,
  -- construct the lindenbaum completion CΓ of Γ
  rcases lindenbaum_lemma Γ hcon with ⟨CΓ, hsuper, hcomp, hcon⟩,
  simp [satisfiable],
  -- build a model out of CΓ
  use lindenbaum_model CΓ,
  -- for every sentence γ ∈ Γ,
  intros γ hγ,
  -- it is entailed by the model iff γ ∈ CΓ (by the truth lemma)
  rw truth_lemma CΓ hcomp hcon,
  -- but that's easy to show since Γ ⊆ CΓ
  apply hsuper,
  exact hγ
end

theorem completeness [denumerable vars] {Γ : set (Form vars)} {A : Form vars} 
  : (Γ ⊨ A) → (Γ ⊩ A) :=
begin
  intro hA,
  -- We rely on the fact that if Γ ⊨ A, then insert (~ A) Γ ⊨ ⊥ 
  have : ¬ satisfiable (insert (~ A) Γ), {
    rw [satisfiable_iff, entail], simp,
    intros v hnA hΓ,
    -- since hA : Γ ⊨ A, and hΓ : v ⊨ Γ, then also v ⊨ A
    specialize hA v hΓ,
    -- but this contradicts with the fact that hnA : v ⊨ ~ A
    -- which allows us to prove falsehood
    simp [eval] at hnA,
    simp [hnA] at hA,
    -- but falsehood is equivalent to entailing ⊥, 
    -- which is exactly what we need
    simp [eval],
    exact hA
  },
  -- By the completeness' theorem, we can conclude that (~ A) :: Γ is 
  -- inconsistent, so (~ A) :: Γ ⊩ ⊥.
  have : ¬ consistent (insert (~ A) Γ) := mt completeness' this,
  simp [consistent] at this,
  -- Applying the Contra derivation step, we find exactly what we need.
  exact Deriv.Contra this
end

#lint