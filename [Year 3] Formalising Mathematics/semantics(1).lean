import syntax
import typing_relation
import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fv : Type} [fvar fv] [const con gnd]

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

--noncomputable because it uses limits.has_limit, which uses classical.choice
noncomputable def eval_type (G : gnd → 𝓒) : type gnd → 𝓒 :=
begin
  refine type.rec _ _ _ _,
  exact G,
  exact ⊤_𝓒,
  { intros A1 A2 rec1 rec2,
    exact rec1 ⨯ rec2, },
  { intros A1 A2 rec1 rec2,
    exact rec1 ⟹ rec2 }
end

notation M `⟦` A `⟧` := eval_type M A

noncomputable def eval_env (G : gnd → 𝓒) : env gnd fv → 𝓒 :=
begin
  refine list.rec _ _,
  exact ⊤_𝓒,
  { rintros ⟨x, A⟩ Γ rec,
    exact eval_type G A ⨯ rec}
end

notation M `⟦` Γ `⟧` := eval_env M Γ

structure model (gnd con 𝓒: Type) [const con gnd] 
[category 𝓒] [limits.has_finite_products 𝓒] [cartesian_closed 𝓒] :=
(G : gnd → 𝓒)
(C : Π c: con, ⊤_𝓒 ⟶ G⟦const.type_of c⟧)

variables {Γ : env gnd fv} {t : term gnd con fv} {A : type gnd}

set_option pp.proofs true

noncomputable def eval_has_type
(M : model gnd con 𝓒)
: (Γ ⊩ t ∷ A) → (M.G⟦Γ⟧ ⟶ M.G⟦A⟧) :=
begin
  -- the recursion syntax outside tactic mode gives a non-wf recursion error,
  -- so I use tactic mode
  intros 𝓙,
  induction 𝓙,
  case has_type.Fvar : Γ x A {
    -- M⟦Γ⟧ ⨯ M⟦A⟧ -π₂-> M⟦A⟧
    exact limits.prod.fst
  },
  case has_type.Fvar' : Γ x y A A' _ _ rec rec_ret {
    -- M⟦Γ⟧ ⨯ M⟦A'⟧ -π₁-> M⟦Γ⟧ -rec_ret → M⟦A⟧
    exact limits.prod.snd ≫ rec_ret,
  },
  case has_type.Const : Γ c {
    -- M⟦Γ⟧ -⟨⟩-> ⊤ -M.C-> M⟦con_type c⟧
    exact terminal.from (M.G⟦Γ⟧) ≫ M.C c
  },
  case has_type.Unit : Γ {
    -- M⟦Γ⟧ -⟨⟩-> ⊤
    exact terminal.from (M.G⟦Γ⟧)
  },
  case has_type.Pair : Γ t t' A A' rec rec' rec_ret rec_ret' {
    -- M⟦Γ⟧ -⟨rec_ret, rec_ret'⟩-> M⟦A ∏ A'⟧
    exact prod.lift rec_ret rec_ret',
  },
  case has_type.Fst : Γ t A A' rec rec_ret {
    -- M⟦Γ⟧ -rec_ret-> M⟦A ∏ A'⟧ -fst-> M⟦A⟧
    exact rec_ret ≫ limits.prod.fst,
  },
  case has_type.Snd : Γ t A A' rec rec_ret {
    -- M⟦Γ⟧ -rec_ret-> M⟦A ∏ A'⟧ -fst-> M⟦A'⟧
    exact rec_ret ≫ limits.prod.snd,
  },
  case has_type.Abs : Γ t A A' rec rec_ret {
    -- M⟦A⟧ ⨯ M⟦Γ⟧ -rec_ret x hfresh-> M⟦A'⟧
    -- so M⟦Γ⟧ -curry (rec_ret x hfresh)-> (M⟦A⟧ ⟹ M⟦A'⟧)
    set x := fvar.fresh (free_vars t ∪ (list.keys Γ).to_finset),
    have hfresh := fvar.hfresh (free_vars t ∪ (list.keys Γ).to_finset),
    exact cartesian_closed.curry (rec_ret x hfresh)
  },
  case has_type.App : Γ t t' A A' rec rec' rec_ret rec_ret' {
    -- M⟦Γ⟧ -⟨rec_ret', rec_ret⟩-> (M⟦A⟧ ⟹ M⟦A'⟧) ⨯ M⟦A⟧ -eval-> M⟦A'⟧
    exact prod.lift rec_ret' rec_ret ≫ (exp.ev (M.G⟦A⟧)).app (M.G⟦A'⟧)
  }
end

-- noncomputable def eval_has_type'
-- (M : model gnd con 𝓒) : ∀ {Γ : env gnd fv} {t : term gnd con fv} {A : type gnd},
-- (Γ ⊩ t ∷ A) → (M.G⟦Γ⟧ ⟶ M.G⟦A⟧)
-- | (⟨_, A⟩ :: Γ) ⌊x⌋ _ (has_type.Fvar _) := limits.prod.fst
-- | (⟨y, A'⟩ :: Γ) ⌊x⌋ A (has_type.Fvar' _ _ rec) :=
-- limits.prod.snd ≫ eval_has_type' rec
-- | Γ |c| A (has_type.Const _) := terminal.from (M.G⟦Γ⟧) ≫ M.C c
-- | Γ ⟪⟫ unit (has_type.Unit _) := terminal.from (M.G⟦Γ⟧)
-- | Γ ⟪t1, t2⟫ (A ∏ B) (has_type.Pair rec1 rec2) := 
-- prod.lift (eval_has_type' rec1) (eval_has_type' rec2)
-- | Γ (fst t) A (has_type.Fst rec) := 
-- eval_has_type' rec ≫ by { unfold eval_type, exact limits.prod.fst}
-- | Γ (snd t) B (has_type.Snd rec) :=
-- eval_has_type' rec ≫ by { unfold eval_type, exact limits.prod.snd}
-- | Γ (Λ A. t) (_ ⊃ B) (has_type.Abs rec) := 
-- by {
--   have hfresh := fvar.hfresh (free_vars t ∪ (list.keys Γ).to_finset),
--   set x := fvar.fresh (free_vars t ∪ (list.keys Γ).to_finset),
--   have rec_ret := eval_has_type' (rec x hfresh),
--   exact cartesian_closed.curry rec_ret}
-- | Γ (t1 ⬝ t2) A1 (@has_type.App _ _ _ _ _ _ _ _ A2 _ rec1 rec2) :=
-- by {
--   have rec_ret1 := eval_has_type' rec1, unfold eval_type at rec_ret1,
--   have rec_ret2 := eval_has_type' rec2,
--   exact prod.lift rec_ret2 rec_ret1 ≫ (exp.ev (M.G⟦A2⟧)).app (M.G⟦A1⟧)
-- }

notation M `⟦` 𝓙 `⟧` := eval_has_type M 𝓙
