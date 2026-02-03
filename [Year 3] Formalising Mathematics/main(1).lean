import soundness
import completeness

/- With the soundness and completeness theorems, we can now show the equivalence
of syntactic derivation to semantic entailment. We use this to prove the
semantic compactness theorem as a corollary. -/

variables {vars : Type} [denumerable vars] {Γ : set (Form vars)} {A : Form vars}

theorem deriv_iff_entail : (Γ ⊩ A) ↔ (Γ ⊨ A) :=
begin
  split,
  exact soundness,
  exact completeness
end

theorem consistent_iff_satisfiable : consistent Γ ↔ satisfiable Γ :=
begin
  rw [satisfiable_iff],
  split,
  exact mt completeness,
  exact mt soundness
end

/-- A corollary of the soundness + completeness theorem is semantic compactness:
If Γ ⊨ A, then A is entailed also by a finite subset of Γ. -/
theorem compactness (h : Γ ⊨ A) : ∃ Δ, Δ ⊆ Γ ∧ Δ.finite ∧ (Δ ⊨ A) :=
begin
  rw ←deriv_iff_entail at h,
  have := deriv_compactness h,
  rcases this with ⟨Δ, this⟩,
  use Δ,
  rw ←deriv_iff_entail,
  exact this
end

/-- Alternate form of compactness theorem: 
every finite subset of Γ is satisfiable, then Γ itself is satisfiable. -/
theorem compactness' (hfinsat : ∀ (Δ : set (Form vars)), Δ ⊆ Γ → Δ.finite → satisfiable Δ) 
  : satisfiable Γ := 
begin
rw ←consistent_iff_satisfiable,
apply deriv_compactness',
intro Δ,
specialize hfinsat Δ,
rw ←consistent_iff_satisfiable at hfinsat,
exact hfinsat
end

#lint