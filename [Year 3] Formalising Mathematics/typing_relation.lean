import syntax
import tactic

import data.subtype
import tactic.induction

namespace typing_relation

open term type

variables {gnd con fv : Type} [fvar fv] [const con gnd]

-- Tried alist, it got messy
def env (gnd fv : Type) := list (Σ (_ : fv), type gnd)
instance : has_mem (Σ (_ : fv), type gnd) (env gnd fv) := list.has_mem

inductive ok : env gnd fv → Type
| Nil  : ok []
| Cons : ∀ {Γ x A}, ok Γ → x ∉ Γ.keys → ok (⟨x, A⟩ :: Γ)

theorem ok_unicity {Γ : env gnd fv} (h1 h2 : ok Γ) : h1 = h2 :=
begin
  with_cases { induction' Γ fixing *; cases h1; cases h2 },
  case list.nil
  { refl },
  case list.cons : Γ ih x A h1 hx1 h2 hx2 
  { rw ih h1 h2 }
end

theorem nodupkeys_of_ok {Γ : env gnd fv} (hΓ : ok Γ) : Γ.nodupkeys :=
begin
  induction hΓ,
  case ok.Nil { exact list.nodupkeys_nil },
  case ok.Cons : Γ x A hΓ hx ih {
    simp only [list.nodupkeys_cons],
    exact ⟨hx, ih⟩
  }
end

-- This has to be a Type, since we interpret the structure of derivations
-- into morphisms in a category for the semantics. Making it Prop would make it
-- impossible to pattern match on the structure of the derivations, since proofs
-- are erased.
inductive has_type : env gnd fv → term gnd con fv → type gnd → Type

| Fvar  : ∀ {Γ : env gnd fv} {x : fv} {A : type gnd},
ok (⟨x, A⟩ :: Γ)
------------------------------
→ has_type (⟨x, A⟩ :: Γ) ⌊x⌋ A

| Fvar' : ∀ {Γ : env gnd fv} {x y : fv} {A A' : type gnd},
y ∉ Γ.keys → x ≠ y → has_type Γ ⌊x⌋ A
-------------------------------------
→ has_type (⟨y, A'⟩ :: Γ) ⌊x⌋ A

| Const : ∀ {Γ c},
ok Γ
-------------------------------
→ has_type Γ (|c|) (const.type_of c)

| Unit : ∀ {Γ},
ok Γ
--------------------
→ has_type Γ ⟪⟫ unit

| Pair : ∀ {Γ t t' A A'},
has_type Γ t A → has_type Γ t' A'
-------------------------------------
→ has_type Γ ⟪t, t'⟫ (A ∏ A')

| Fst : ∀ {Γ t A A'},
has_type Γ t (A ∏ A')
------------------------
→ has_type Γ (fst t) A

| Snd : ∀ {Γ t A A'},
has_type Γ t (A ∏ A')
-------------------------
→ has_type Γ (snd t) A'

-- Since has_type is a Type not Prop, this should really be Π not ∀, but it's
-- helpful to think of it as like a Prop with proof-relevance.
| Abs : ∀ {Γ : env gnd fv} {t A A'},
(∀ x ∉ free_vars t ∪ Γ.keys.to_finset, has_type (⟨x, A⟩ :: Γ) (open_var x 0 t) A')
--------------------------------------------------------------------------------
→ has_type Γ (Λ A. t) (A ⊃ A')

| App : ∀ {Γ t t' A A'},
has_type Γ t (A ⊃ A') → has_type Γ t' A
---------------------------------------------
→ has_type Γ (t ⬝ t') A'

notation Γ ` ⊩ ` t ` ∷ ` A := has_type Γ t A

variables {Γ : env gnd fv} {t t1 t2 : term gnd con fv} {A A1 A2 B C : type gnd}
          {x y : fv}

lemma mem_of_has_type_fv (h : Γ ⊩ (⌊x⌋ : term gnd con fv) ∷ A)
: sigma.mk x A ∈ Γ :=
begin
  induction' h,
  { simp },
  { simp only [list.mem_cons_iff, heq_iff_eq], right, exact ih }
end

lemma ok_of_has_type (h : Γ ⊩ t ∷ A) : ok Γ :=
begin
  induction' h,
  case typing_relation.has_type.Fvar
  { exact x_1 },
  case typing_relation.has_type.Fvar' : Γ x y A A' h h_1 h_2 ih
  { apply ok.Cons, exact ih, exact h },
  case typing_relation.has_type.Const : Γ c
  { exact x },
  case typing_relation.has_type.Unit
  { exact x },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 },
  case typing_relation.has_type.Fst : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Snd : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Abs : Γ t1 A B h ih
  { set x := fvar.fresh (free_vars t1 ∪ Γ.keys.to_finset),
    have hfresh := fvar.hfresh (free_vars t1 ∪ Γ.keys.to_finset),
    specialize @ih x hfresh,
    cases' ih,
    exact ih
  },
  case typing_relation.has_type.App : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 }
end

lemma lc_of_has_type (h : Γ ⊩ t ∷ A) : locally_closed Γ.keys.to_finset t :=
begin
  induction' h,
  case typing_relation.has_type.Fvar : Γ x A h
  { apply locally_closed.Fvar, 
    simp only [list.keys_cons, list.to_finset_cons, finset.mem_insert,
               eq_self_iff_true, true_or]
  },
  case typing_relation.has_type.Fvar' : Γ x y A A' h h_1 h_2 ih
  { apply locally_closed.Fvar, 
    cases' ih,
    simp only [list.keys_cons, list.to_finset_cons, finset.mem_insert, 
               list.mem_to_finset] at h_3 ⊢,
    right,
    exact h_3
  },
  case typing_relation.has_type.Const : Γ c h
  { exact locally_closed.Const },
  case typing_relation.has_type.Unit : Γ h
  { exact locally_closed.Unit },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact locally_closed.Pair ih1 ih2 },
  case typing_relation.has_type.Fst : Γ t A A' h ih
  { exact locally_closed.Fst ih },
  case typing_relation.has_type.Snd : Γ t A A_1 h ih
  { exact locally_closed.Snd ih },
  case typing_relation.has_type.Abs : Γ t A A_1 h ih
  { apply locally_closed.Abs,
    intros x hx,
    specialize h x hx,
    specialize ih x hx,
    simp at ih,
    exact ih
  },
  case typing_relation.has_type.App : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact locally_closed.App ih1 ih2 },
end

theorem type_unicity (h1 : Γ ⊩ t ∷ A1) (h2 : Γ ⊩ t ∷ A2) : A1 = A2 :=
begin
  have ht := lc_of_has_type h1,
  with_cases {induction' ht generalizing Γ A1 A2 t; cases h1; cases h2},
  case locally_closed.Const { refl },
  case locally_closed.Unit { refl },
  case locally_closed.Pair
  : _ t1 t2 hlc1 hlc2 ih1 ih2 A1 A2 h1t1 h1t2 B1 B2 h2t1 h2t2 {
    simp only,
    split,
    exact ih1 h1t1 h2t1,
    exact ih2 h1t2 h2t2
  },
  case locally_closed.Fst : _ A1 A2 t hlc ih B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.left
  },
  case locally_closed.Snd : _ A1 A2 t hlc ih B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.right
  },
  case locally_closed.Abs : _ B t hlc ih A1 h1 A2 h2 {
    simp only [eq_self_iff_true, true_and],
    have hfresh := fvar.hfresh (free_vars t ∪ (list.keys Γ).to_finset),
    set x := fvar.fresh (free_vars t ∪ (list.keys Γ).to_finset),
    specialize h1 x hfresh,
    specialize h2 x hfresh,
    refine ih x hfresh _ h1 h2,
    simp, 
  },
  case locally_closed.App 
  : _  A1 A2 t1 t2 hlc1 hlc2 ih1 ih2 B1 h1t2 h1t1 B2 h2t2 h2t1 {
    specialize ih1 h1t1 h2t1,
    simp only at ih1,
    exact ih1.right,
  },
  case has_type.Fvar has_type.Fvar { refl },
  case has_type.Fvar has_type.Fvar' { contradiction },
  case has_type.Fvar' has_type.Fvar { contradiction },
  case has_type.Fvar' has_type.Fvar' : _ A1 A2 x hx y A' hy hneq h1 _ _ h2 { 
    have hnodup := nodupkeys_of_ok (ok_of_has_type h1),
    exact hnodup.eq_of_mk_mem (mem_of_has_type_fv h1) (mem_of_has_type_fv h2)
  }
end 

theorem deriv_unicity (h1 h2 : Γ ⊩ t ∷ A) : h1 = h2 :=
begin
  have ht := lc_of_has_type h1,
  --set FV := (list.keys Γ).to_finset,
  with_cases {induction' ht generalizing Γ A t; cases h1; cases h2},

  case locally_closed.Const : _ c h1 h2 { rw ok_unicity h1 h2 },
  case locally_closed.Unit : _ h1 h2 { rw ok_unicity h1 h2 },
  case locally_closed.Pair 
  : _ t1 t2 hlc1 hlc2 ih1 ih2 A B h1t1 h1t2 h2t1 h2t2 {
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2
  },
  case locally_closed.Fst : _ A t hlc ih B1 h1 B2 h2 {
    have := type_unicity h1 h2,
    simp only [eq_self_iff_true, true_and] at this,
    subst this,
    rw ih h1 h2,
  },
  case locally_closed.Snd : _ A t hlc ih B1 h1 B2 h2 {
    have := type_unicity h1 h2,
    simp only [eq_self_iff_true, and_true] at this,
    subst this,
    rw ih h1 h2,
  },
  case locally_closed.Abs : _ A t hlc ih B h1 h2 {
    -- this looks easy now, but actually needed induction', otherwise the ih
    -- came in the wrong form and couldnt be used because it was not tracking enough
    -- info about the local closure hlc
    simp only,
    ext x hx,
    refine ih x hx _ (h1 x hx) (h2 x hx),
    simp,
  },
  case locally_closed.App
  : _ B t1 t2 hlc1 hlc2 ih1 ih2 A1 h1t2 h1t1 A2 h2t2 h2t1 {
    have := type_unicity h1t2 h2t2,
    subst this,
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2,
  },
  case has_type.Fvar has_type.Fvar : _ A x h1 hx h2 { rw ok_unicity h1 h2 },
  case has_type.Fvar has_type.Fvar' { contradiction },
  case has_type.Fvar' has_type.Fvar { contradiction },
  case has_type.Fvar' has_type.Fvar' : A1 x Γ y A2 hy hx hneq h1 hy' hneq' h2 {
    simp only,
    with_cases { induction' Γ fixing *; cases h1; cases h2 },
    case has_type.Fvar has_type.Fvar : _ _ _ _ _ h1 h2
    { rw ok_unicity h1 h2 },
    case has_type.Fvar has_type.Fvar'
    { contradiction },
    case has_type.Fvar' has_type.Fvar
    { contradiction },
    case has_type.Fvar' has_type.Fvar' 
    : Γ ih x' A' hy _ hy' h1x' h1neqx' h1 h2x' h2neqx' h2
    { simp only,
      simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff] at hy,
      refine ih hy.right _ h1 hy.right h2,
      simp only [list.keys_cons, list.to_finset_cons, finset.mem_insert, 
                 list.mem_to_finset] at ⊢ hx,
      rcases hx with (hx | hx | hx),
      { left, exact hx }, { contradiction }, {right, exact hx}
    },
  }
end

lemma exchange (h : ⟨x, A⟩::⟨y, B⟩::Γ ⊩ t ∷ C) : ⟨y, B⟩::⟨x, A⟩::Γ ⊩ t ∷ C :=
begin
  sorry
  -- no time!
end

-- I realised (too late) I probably should've followed the 
lemma weakening (hx : x ∉ free_vars t ∪ Γ.keys.to_finset)
(h : Γ ⊩ t ∷ A) : (⟨x, B⟩::Γ) ⊩ t ∷ A :=
begin
  induction' h generalizing Γ t A,
  case typing_relation.has_type.Fvar : Γ x_1 A h
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset] at hx,
    apply has_type.Fvar',
    { simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff], 
      exact ⟨hx.left, hx.right.right⟩ },
    { symmetry, exact hx.left },
    exact has_type.Fvar h
  },
  case typing_relation.has_type.Fvar' : Γ x_1 y A A' h h_1 h_2 ih
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.Fvar',
    { simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff], 
      exact ⟨hx.left, hx.right.right⟩ },
    { symmetry, exact hx.right.left },
    apply has_type.Fvar',
    { exact h }, { exact h_1 },
    exact h_2
  },
  case typing_relation.has_type.Const : Γ c h
  { apply has_type.Const,
    apply ok.Cons,
    exact h,
    simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
              finset.union_insert, finset.mem_insert, finset.mem_union,
              list.mem_to_finset] at hx,
    exact hx.right,
  },
  case typing_relation.has_type.Unit : Γ h
  { apply has_type.Unit,
    apply ok.Cons,
    exact h,
    simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
              finset.union_insert, finset.mem_insert, finset.mem_union,
              list.mem_to_finset] at hx,
    exact hx.right,
  },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.Pair,
    { apply ih1, 
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.left, hx.right⟩
    },
    { apply ih2,
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.right, hx.right⟩
    }
  },
  case typing_relation.has_type.Fst : Γ t A A' h ih
  { apply has_type.Fst, exact ih hx },
  case typing_relation.has_type.Snd : Γ t A A_1 h ih
  { apply has_type.Snd, exact ih hx },
  case typing_relation.has_type.Abs : Γ t A A_1 h ih
  { apply has_type.Abs, intros x1 hx1,
    /- actually might need to strengthen the goal to
       (h : Δ ++ Γ ⊩ t ∷ A) : (Δ ++ ⟨x, B⟩::Γ) ⊩ t ∷ A,
       and maybe need exchange lemma? -/
    sorry 
  },
  case typing_relation.has_type.App : Γ t1 t2 A B h1 h2 ih1 ih2
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.App,
    { apply ih1, 
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.left, hx.right⟩
    },
    { apply ih2,
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.right, hx.right⟩
    } 
  },
end

lemma subst_preserves_type
(h1 : (⟨x, A1⟩::Γ ⊩ t2 ∷ A2)) (h2 : (Γ ⊩ t1 ∷ A1))
: (Γ ⊩ (subst t1 x t2) ∷ A2) :=
begin
  have ht2 := lc_of_has_type h1,
  induction' ht2 generalizing Γ x t1 t2 A1 A2 h2,
  case term.locally_closed.Const : t2
  { simp only [subst],
    cases' h1, 
    apply has_type.Const,
    cases' x_1,
    exact x_1
  },
  case term.locally_closed.Fvar : t
  { simp only [subst],
    split_ifs,
    { subst h_1, cases' h1, { exact h2 }, { contradiction } },
    { cases' h1, { contradiction }, { exact h1 } }
  },
  case term.locally_closed.Unit
  { simp only [subst],
    cases' h1,
    apply has_type.Unit,
    cases' x_1,
    exact x_1
  },
  case term.locally_closed.Pair : t2l t2r ht2l ht2r ihl ihr
  { simp only [subst],
    cases' h1,
    specialize ihl h2 h1,
    specialize ihr h2 h1_1,
    exact has_type.Pair ihl ihr
  },
  case term.locally_closed.Fst : t2 ht2 ih
  { simp only [subst],
    cases' h1,
    exact has_type.Fst (ih h2 h1)
  },
  case term.locally_closed.Snd : t2 ht2 ih
  { simp only [subst],
    cases' h1,
    exact has_type.Snd (ih h2 h1)
  },
  case term.locally_closed.Abs : A1 t2 ht2 ih
  { simp only [subst],
    cases' h1,
    apply has_type.Abs,
    intros x1 hx1,
    -- This should be doable in principle, need to show a similar lemma to 
    -- free_vars_open_term but for free_vars_subst instead.
    -- also need to show commutativity between subst and open_var...
    sorry
  },
  case term.locally_closed.App : t2l t2r ht2l ht2r ihl ihr
  { simp only [subst],
    cases' h1,
    specialize ihl h2 h1,
    specialize ihr h2 h1_1,
    exact has_type.App ihl ihr
  }
end

lemma free_vars_subset_env (h : Γ ⊩ t ∷ A) : free_vars t ⊆ Γ.keys.to_finset :=
begin
  induction' h,
  case typing_relation.has_type.Fvar : Γ x A x_1
  { simp only [free_vars, list.keys_cons, list.to_finset_cons, 
               finset.singleton_subset_iff, finset.mem_insert, eq_self_iff_true,
               true_or], 
  },
  case typing_relation.has_type.Fvar' : Γ x y A A' h h_1 h_2 ih
  { simp only [free_vars, list.keys_cons, list.to_finset_cons, 
               finset.singleton_subset_iff, finset.mem_insert, list.mem_to_finset] 
               at ⊢ ih,
    right, exact ih
  },
  case typing_relation.has_type.Const : Γ c x
  { simp only [free_vars, finset.empty_subset] },
  case typing_relation.has_type.Unit : Γ x
  { simp only [free_vars, finset.empty_subset] },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { simp only [free_vars], exact finset.union_subset ih1 ih2 },
  case typing_relation.has_type.Fst : Γ t A A' h ih
  { simp only [free_vars], exact ih },
  case typing_relation.has_type.Snd : Γ t A A_1 h ih
  { simp only [free_vars], exact ih },
  case typing_relation.has_type.Abs : Γ t A A_1 h ih
  { have hfresh := fvar.hfresh (free_vars t ∪ (list.keys Γ).to_finset),
    set x := fvar.fresh (free_vars t ∪ (list.keys Γ).to_finset),
    specialize ih x hfresh,
    specialize h x hfresh,
    simp only [free_vars],
    have := free_vars_open_var t x 0,
    cases this,
    all_goals { 
      simp only [this, finset.insert_eq, list.keys_cons, list.to_finset_cons] at ih,
      rw finset.subset_iff; intros x' hx',
    },
    -- do this for first goal
    any_goals {specialize ih (finset.subset_union_left _ _ hx')},
    -- do this for second goal
    any_goals {specialize ih hx'},
    -- and then same steps across both goals again
    all_goals {
      cases finset.mem_union.mp ih,
      { exfalso, rw finset.mem_singleton at h_1, rw h_1 at hx',
        rw finset.not_mem_union at hfresh, exact hfresh.left hx' },
      { exact h_1 },
    }
  },
  case typing_relation.has_type.App : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { simp only [free_vars], exact finset.union_subset ih1 ih2 },
end

end typing_relation