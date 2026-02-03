import syntax
import typing_relation
import semantics

import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

namespace term_equality

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fv : Type} [fvar fv] [const con gnd]
variables {con_type : con → type gnd}

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

inductive beta_eta_eq (con_type : con → type gnd)
: env gnd fv → term gnd con fv → term gnd con fv → type gnd → Type
| Refl : ∀ {Γ t A},
(Γ ⊩ t ∷ A)
-----------------------
→ beta_eta_eq Γ t t A 

| Symm : ∀ {Γ t1 t2 A},
beta_eta_eq Γ t1 t2 A
------------------------
→ beta_eta_eq Γ t2 t1 A 

| Trans : ∀ {Γ t1 t2 t3 A},
beta_eta_eq Γ t1 t2 A → beta_eta_eq Γ t2 t3 A
---------------------------------------------
→ beta_eta_eq Γ t1 t3 A

| Beta_fun : ∀ {Γ : env gnd fv} {t1 t2 : term gnd con fv} {A B},
(Γ ⊩ (Λ A. t1) ∷ (A ⊃ B))
→ (Γ ⊩ t2 ∷ A)
----------------------------------------------------------
→ beta_eta_eq Γ ((Λ A. t1) ⬝ t2) (open_term t2 0 t1) B

| Beta_prod_fst : ∀ {Γ t1 t2 A B},
(Γ ⊩ t1 ∷ A) → (Γ ⊩ t2 ∷ B)
---------------------------------------------------
→ beta_eta_eq Γ (fst ⟪t1, t2⟫) t1 A

| Beta_prod_snd : ∀ {Γ t1 t2 A B},
(Γ ⊩ t1 ∷ A) → (Γ ⊩ t2 ∷ B)
---------------------------------------------------
→ beta_eta_eq Γ (snd ⟪t1, t2⟫) t2 B

| Eta_fun : ∀ {Γ t A B},
(Γ ⊩ t ∷ (A ⊃ B))
-----------------------------------------
→ beta_eta_eq Γ t (Λ A. (t ⬝ ⌈0⌉)) (A ⊃ B) 

| Eta_prod : ∀ {Γ t A B},
(Γ ⊩ t ∷ (A ∏ B))
----------------------------------------
→ beta_eta_eq Γ t ⟪fst t, snd t⟫ (A ∏ B)  

| Eta_unit : ∀ {Γ t},
(Γ ⊩ t ∷ unit)
--------------------------
→ beta_eta_eq Γ t ⟪⟫ unit

| Cong_lam : ∀ {Γ : env gnd fv} {t t' A B},
(∀ x ∉ free_vars t ∪ Γ.keys.to_finset, 
  beta_eta_eq (⟨x, A⟩ :: Γ) (open_var x 0 t) (open_var x 0 t') B)
----------------------------------------------------------------
→ beta_eta_eq Γ (Λ A. t) (Λ A. t') (A ⊃ B)

| Cong_app : ∀ {Γ t1 t2 t1' t2' A B},
beta_eta_eq Γ t1 t1' (A ⊃ B) → beta_eta_eq Γ t2 t2' A
-----------------------------------------------------
→ beta_eta_eq Γ (t1 ⬝ t2) (t1' ⬝ t2') B

| Cong_fst : ∀ {Γ t t' A B},
beta_eta_eq Γ t t' (A ∏ B)
----------------------------------
→ beta_eta_eq Γ (fst t) (fst t') A

| Cong_snd : ∀ {Γ t t' A B},
beta_eta_eq Γ t t' (A ∏ B)
----------------------------------
→ beta_eta_eq Γ (snd t) (snd t') B

| Cong_pair : ∀ {Γ t1 t2 t1' t2' A B},
beta_eta_eq Γ t1 t1' A → beta_eta_eq Γ t2 t2' B
-----------------------------------------------
→ beta_eta_eq Γ ⟪t1, t2⟫ ⟪t1', t2'⟫ (A ∏ B)

lemma has_type_of_beta_eta_eq {Γ : env gnd fv} 
{t1 t2 : term gnd con fv} {A : type gnd} 
(heq : beta_eta_eq con_type Γ t1 t2 A)
: (Γ ⊩ t1 ∷ A) × (Γ ⊩ t2 ∷ A) :=
begin
  induction' heq generalizing Γ t1 t2 A,
  case term_equality.beta_eta_eq.Refl : Γ t A h
  { exact ⟨h, h⟩ },
  case term_equality.beta_eta_eq.Symm : Γ t1 t2 A rec ih
  { exact prod.swap ih },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2
  { exact ⟨ih1.fst, ih2.snd⟩ },
  case term_equality.beta_eta_eq.Beta_fun : Γ t1 t2 A B h1 h2
  { refine ⟨h1.App h2, _⟩,
    cases' h1,
    have hfresh := fvar.hfresh (free_vars t ∪ (list.keys Γ).to_finset),
    set x := fvar.fresh (free_vars t ∪ (list.keys Γ).to_finset),
    specialize h1 x hfresh,
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hfresh,
    rw open_term_eq_subst_of_open_var t t2 x 0 hfresh.left,
    exact subst_preserves_type h1 h2
  },
  case term_equality.beta_eta_eq.Beta_prod_fst : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Fst, h1⟩ },
  case term_equality.beta_eta_eq.Beta_prod_snd : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Snd, h2⟩ },
  case term_equality.beta_eta_eq.Eta_fun : Γ t A B h
  { refine ⟨h, _⟩,
    apply has_type.Abs,
    intros x hx,
    simp only [open_var, open_term, eq_self_iff_true, if_true],
    apply has_type.App, rotate 2,
    exact A,
    sorry,
    /- from h we can derive that t is locally closed, so open_term does nothing -/
    /- then, we need weakening... -/
    apply has_type.Fvar,
    apply ok.Cons (ok_of_has_type h),
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hx,
    exact hx.right
    },
  case term_equality.beta_eta_eq.Eta_prod : Γ t A1 A2 h
  { exact ⟨h, h.Fst.Pair h.Snd⟩ },
  case term_equality.beta_eta_eq.Eta_unit : Γ t1 h
  { exact ⟨h, has_type.Unit (ok_of_has_type h)⟩ },
  case term_equality.beta_eta_eq.Cong_lam : Γ t1 t2 A1 A2 heq ih
  { let ih1 := λ x hx, (ih x hx).fst,
    -- to make this useable, we need hx to be x ∉ t2, not x ∉ t1
    -- but we need x ∉ t1 to use ih.
    -- I thought I could use free_vars_subset_env, but I realize there's no
    -- proof of Γ ⊩ open_var x 0 t ∷ A2 I can use!
    -- this would be doable if I had the cofinite quantification
    -- but that's not possible in lean 3
    let ih2 : Π (x : fv), x ∉ free_vars t2 ∪ (list.keys Γ).to_finset →
              (⟨x, A1⟩ :: Γ ⊩ open_var x 0 t2 ∷ A2) := λ x hx, by {
      rw finset.not_mem_union at hx,
      sorry
    },
    exact ⟨has_type.Abs ih1, has_type.Abs ih2⟩
  },
  case term_equality.beta_eta_eq.Cong_app : Γ t1 t2 t1' t2' A1 A2 heq heq_1 ih1 ih2
  { exact ⟨ih1.fst.App ih2.fst, ih1.snd.App ih2.snd⟩ },
  case term_equality.beta_eta_eq.Cong_fst : Γ t1 t2 A B heq ih
  { exact ⟨ih.fst.Fst, ih.snd.Fst⟩ },
  case term_equality.beta_eta_eq.Cong_snd : Γ t1 t2 A A_1 heq ih
  { exact ⟨ih.fst.Snd, ih.snd.Snd⟩ },
  case term_equality.beta_eta_eq.Cong_pair : Γ t1 t2 t1' t2' A1 A2 heq heq_1 ih1 ih2
  { exact ⟨ih1.fst.Pair ih2.fst, ih1.snd.Pair ih2.snd⟩ }
end

universes u v
variables {C : Type u} [category.{v} C]
lemma comp_cong {X Y Z : C} {f1 f2 : X ⟶ Y} {g : Y ⟶ Z} (h : f1 = f2)
: f1 ≫ g = f2 ≫ g :=
begin
  rw h
end

theorem soundness {M : model gnd con 𝓒} 
{Γ : env gnd fv} {t1 t2 : term gnd con fv} {A : type gnd}
(h1 : Γ ⊩ t1 ∷ A) (h2 : Γ ⊩ t2 ∷ A)
(heq : beta_eta_eq con_type Γ t1 t2 A)
: (M⟦h1⟧) = (M⟦h2⟧) :=
begin
  induction' heq generalizing Γ t1 t2 A,
  case beta_eta_eq.Refl : Γ t A { rw deriv_unicity h1 h2 },
  case term_equality.beta_eta_eq.Symm : Γ t2 t1 A rec ih {
    symmetry, exact ih h2 h1,
  },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2 {
    rename [h2 → h3],
    obtain ⟨_, h2⟩ := has_type_of_beta_eta_eq rec1,
    exact trans (ih1 h1 h2) (ih2 h2 h3)
  },
  case term_equality.beta_eta_eq.Beta_fun : Γ t1 t2 A A_1 x x_1
  { -- we need to talk about semantics of substitution
    -- not enough time to do that =(
    admit  },
  case term_equality.beta_eta_eq.Beta_prod_fst : Γ t1 t1_1 A B x x_1
  { cases' h1, cases h1, rw deriv_unicity h2 h1_ᾰ, simp [eval_has_type] },
  case term_equality.beta_eta_eq.Beta_prod_snd : Γ t1 t2 A1 A2 x x_1
  { cases' h1, cases h1, rw deriv_unicity h2 h1_ᾰ_1, simp [eval_has_type] },
  case term_equality.beta_eta_eq.Eta_fun : Γ t A A_1 x
  { -- need semantics of weakening...
    admit },
  case term_equality.beta_eta_eq.Eta_prod : Γ t A1 A2 x
  { -- Idea: Due to deriv unicity, we can say that
    -- M⟦h2_left : Γ ⊩ fst t ∷ A1⟧ = π₁ ∘ M⟦h1 : Γ ⊩ t ∷ A1 ∏ A2⟧ 
    -- M⟦h2_right : Γ ⊩ snd t ∷ A1⟧ = π₂ ∘ M⟦h1 : Γ ⊩ t ∷ A1 ∏ A2⟧
    -- so M⟦h2⟧ = ⟨π₁ ∘ M⟦h1⟧, π₂ ∘ M⟦h1⟧⟩ = M⟦h1⟧ by the universal 
    -- property of products.
    cases' h2, cases h2, cases h2_1,
    have := type_unicity h1 h2_ᾰ, simp at this, subst this,
    have := type_unicity h1 h2_1_ᾰ, simp at this, subst this,
    rw deriv_unicity h2_ᾰ h1,
    rw deriv_unicity h2_1_ᾰ h1,
    ext; simp [eval_has_type]
  },
  case term_equality.beta_eta_eq.Eta_unit : Γ t1 x
  { -- M⟦h1⟧ and M⟦h2⟧ are both arrows from M⟦Γ⟧ to the terminal object,
    -- so they must be equal by the uniqueness condition. 
    have := category_theory.limits.unique_to_terminal (M.G⟦Γ⟧),
    exact trans (this.uniq (M⟦h1⟧)) (symm (this.uniq (M⟦h2⟧))),
  },
  case term_equality.beta_eta_eq.Cong_lam : Γ t1 t2 A A_1 heq ih
  { cases h2, cases h1, 
    simp [eval_has_type],
    -- this is the same issue as line 140: one hypothesis is asking for free_vars t1
    -- the other is asking for free_vars t2.
    sorry
  },
  case term_equality.beta_eta_eq.Cong_app : Γ t1 t2 t1' t2' A1 A2 heq heq' ih ih'
  { -- Idea: 
    -- the goal is essentially to show 
    -- eval ∘ ⟨M⟦h1.left⟧, M⟦h1.right⟧⟩ = eval ∘ ⟨M⟦h2.left⟧, M⟦h2.right⟧⟩
    -- By congruence, and by the universal property of products,
    -- This is the same as showing M⟦h1.left⟧ = M⟦h2.left⟧ and M⟦h1.right⟧ = M⟦h2.right⟧
    -- But that's exactly what we have with the inductive hypotheses.
    cases' h2, cases' h1,
    obtain ⟨h1_1', h2_1'⟩ := has_type_of_beta_eta_eq heq',
    have := type_unicity h1_1 h1_1', subst this,
    have := type_unicity h2_1 h2_1', subst this,
    specialize ih h1 h2,
    specialize ih' h1_1 h2_1,
    apply comp_cong,
    ext; simp only [prod.lift_fst, prod.lift_snd],
    exact ih',
    exact ih, 
  },
  case term_equality.beta_eta_eq.Cong_fst : Γ t1 t2 A B heq ih
  { -- showing π₁ ∘ M⟦h1⟧ = π₂ ∘ M⟦h2⟧ is the same as showing M⟦h1⟧ = M⟦h2⟧
    -- by congruence
    cases' h1, cases' h2,
    obtain ⟨h1', h2'⟩ := has_type_of_beta_eta_eq heq,
    have := type_unicity h1 h1', simp at this, subst this,
    have := type_unicity h2 h2', simp at this, subst this,
    apply comp_cong,
    exact ih h1 h2,
  },
  case term_equality.beta_eta_eq.Cong_snd : Γ t1 t2 A A_1 heq ih
  { -- similar to Cong_fst
    cases' h1, cases' h2,
    obtain ⟨h1', h2'⟩ := has_type_of_beta_eta_eq heq,
    have := type_unicity h1 h1', simp at this, subst this,
    have := type_unicity h2 h2', simp at this, subst this,
    apply comp_cong,
    exact ih h1 h2,
  },
  case term_equality.beta_eta_eq.Cong_pair : Γ t1 t2 t1' t2' A1 A2 heq heq' ih ih'
  { -- this uses the universal property of products to decompose equality on
    -- products, as we did in Cong_app.
    cases' h1, cases h2, --sometimes `cases'` just doesn't work even though `cases` does
    ext; simp only [eval_has_type, prod.lift_fst, prod.lift_snd], 
    exact ih h1 h2_ᾰ,
    exact ih' h1_1 h2_ᾰ_1
  }
end


end term_equality