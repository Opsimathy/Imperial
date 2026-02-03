import natural_deduction
import semantics

variables {vars : Type} {Γ : set (Form vars)} {A B C : Form vars}

theorem soundness : (Γ ⊩ A) → (Γ ⊨ A) :=
begin
  -- induce on the structure of the derivation
  -- but before that we unwrap definitions and introduce hypotheses
  -- to avoid repeating the process in each case
  intro deriv,
  rw entail,
  intros v hΓ,
  induction deriv,
  case Deriv.Bottom_E : Γ A h ih {
   -- the ih can be used to derive falsehood, from which anything follows
   specialize ih hΓ,
   simp [eval] at ih,
   exfalso,
   exact ih,
  },
  case Deriv.Ax : Γ A h {
   exact hΓ A h,
  },
  case Deriv.Not_I : Γ A h ih {
   -- see what the goal really is (when simplified) first
   simp [eval],
   -- we need A to evaluate to truth in order to use the ih,
   -- so try to prove by contradiction as it assumes exactly this
   by_contra hA,
   simp at hA,
   -- use the ih: we first have to prove the precedent in the
   -- exactly required form
   have : ∀ (γ : Form vars), γ ∈ (insert A Γ) → (↥⟦γ⟧_ v),
   { -- either γ is A or its in Γ
     intros γ hγ,
     simp at hγ, cases hγ,
     {rw hγ, exact hA}, -- in the former case, we use hA
     {exact hΓ γ hγ}    -- in the latter case, we use hΓ
   },
   specialize ih this,
   -- now the evaluation of the ih is really just falsehood, exactly what we 
   -- need
   simp [eval] at ih,
   exact ih
  },
  case Deriv.Not_E : Γ A h₁ h₂ ih₁ ih₂ {
   -- ih₁ and ih₂ have contradicting antecedents, so we first obtain those
   specialize ih₁ hΓ,
   specialize ih₂ hΓ,
   simp [eval] at ih₁ ih₂ ⊢,
   -- form the contradiction to obtain falsehood
   rw ih₁ at ih₂,
   simp at ih₂,
   exact ih₂
  },
  case Deriv.And_I : Γ A B h₁ h₂ ih₁ ih₂ {
   -- similar to case above, but we make A ⋀ B instead of a contradiction 
   specialize ih₁ hΓ,
   specialize ih₂ hΓ,
   simp [eval] at ⊢,
   exact ⟨ih₁, ih₂⟩
  },
  case Deriv.And_E_1 : Γ A B h ih {
   -- take out the truth of A from the truth of A and B
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih with ih₁ ih₂,
   exact ih₁
  },
  case Deriv.And_E_2 : Γ A B h ih {
   -- As in the previous case, but we want B
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih with ih₁ ih₂,
   exact ih₂
  },
  case Deriv.Or_I_1 : Γ A B h ih {
   specialize ih hΓ,
   simp [eval],
   left,
   exact ih
  },
  case Deriv.Or_I_2 : Γ A B h ih {
   specialize ih hΓ,
   simp [eval],
   right,
   exact ih
  },
  case Deriv.Or_E : Γ A B C h h₁ h₂ ih ih₁ ih₂ {
   -- the antecedent of ih₁ and ih₂ both are the goal we want,
   -- but we cannot apply them directly as this would require proving that A 
   -- (respectively B) evaluates to true. This we cannot do. Instead use ih 
   -- to obtain the A ⋁ B, which allows an analysis by cases.
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih,
   -- from here, we can use ih₁ in the first case and ih₂ in the second.
   {
     apply ih₁,
     intros γ hγ,
     cases hγ,
     {rw hγ, exact ih}, -- if γ = A
     {exact hΓ γ hγ}    -- if γ in Γ
   },
   {
     apply ih₂,
     intros γ hγ,
     cases hγ,
     {rw hγ, exact ih}, -- if γ = A
     {exact hΓ γ hγ}    -- if γ in Γ
   },
  },
  case Deriv.Contra : Γ A h ih {
   -- as with Not_I, we need a proof by contradiction.
   -- the structure of the proof is very similar.
   by_contra hA,
   simp [eval] at hA,
   have : ∀ (γ : Form vars), γ ∈ (insert (~ A) Γ) → (↥⟦γ⟧_ v),
   {
     intros γ hγ,
     simp at hγ, cases hγ,
     {rw hγ, simp [eval], exact hA},
     {exact hΓ γ hγ}
   },
   specialize ih this, simp [eval] at ih,
   exact ih
  },
  case Deriv.Weakening : Γ Γ' A hsub h ih {
    apply ih,
    intros γ hγ,
    apply hΓ,
    apply hsub,
    exact hγ
  }
end  

theorem soundness' : satisfiable Γ → consistent Γ :=
begin
  rw [consistent, satisfiable_iff],
  intro hsat,
  -- suppose towards a contradiction that Γ is inconsistent, so Γ ⊩ ⊥
  by_contra hcon,
  -- by the soundness theorem, Γ ⊨ ⊥, which contradicts Γ being satisfiable
  have : (Γ ⊨ ⊥) := soundness hcon,
  exact hsat this
end

#lint