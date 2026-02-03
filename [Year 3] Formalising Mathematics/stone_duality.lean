import order.category.Frame
import order.hom.complete_lattice
import order_iso
import topology.basic
import topology.category.Top

universes u

open order
open category_theory

/--
A frame is spatial if it "has enough points". More specifically, for any two elements
`a b : L`, if `a` is not less than or equal to `b`, there must exist some point
contained in `a` but not `b`.
-/
class spatial (L : Type u) [frame L] : Prop :=
(enough_points : ∀ {a b : L}, ¬ a ≤ b → ∃ p : frame_hom L Prop, p a ∧ ¬ p b)

/--
Given a frame `L`, the type of its points `frame_hom L Prop` has a natural topology given by
the image of `L` under the function `λ a, {p | p a}`.

We normally think of the elements `a : L` as open subsets. For a point `p : frame_hom L Prop`,
we say that `p` lies in `a` if `p a = ⊤` (or equivalently if `p a` holds). The topological
structure of `frame_hom L Prop` formalises this intuition.
-/
instance pts_topological_space {L : Type u} [frame L] : topological_space (frame_hom L Prop) :=
{ is_open := λ U, ∃ (a : L), U = {p | p a},
  is_open_univ := begin
    use ⊤,
    rw [eq_comm, set.eq_univ_iff_forall],
    simp_rw [map_top],
    exact (λ _, trivial),
  end,
  is_open_inter := begin
    rintros U V ⟨a, rfl⟩ ⟨b, rfl⟩,
    use a ⊓ b,
    ext,
    split,
    { rintro ⟨hxU, hxV⟩,
      change x a at hxU,
      change x b at hxV,
      simp [map_inf, hxU, hxV], },
    { intro hxUV,
      change x (a ⊓ b) at hxUV,
      change x a ∧ x b,
      simpa [map_inf] using hxUV, },
  end,
  is_open_sUnion := begin
    rintros Us hUs,
    use Sup {a : L | {p : frame_hom L Prop | p a} ∈ Us},
    simp_rw [map_Sup, set.image, Sup_Prop_eq],
    ext p,
    split,
    { rintro ⟨U, hU, hpU⟩,
      obtain ⟨a, rfl⟩ := hUs U hU,
      exact ⟨true, ⟨a, hU, eq_true_intro hpU⟩, trivial⟩, },
    { rintro ⟨_, hprop, prop⟩,
      cases eq_true_intro prop,
      obtain ⟨a, ha, ha'⟩ := hprop,
      rw eq_true at ha',
      exact ⟨_, ha, ha'⟩, },
  end,
}

/--
Given a frame morphism `f : frame_hom L M`, we get a continuous map from
`frame_hom M Prop` to `frame_hom L Prop` by post composing points with `f`.
-/
def pts_map {L M : Type u} [frame L] [frame M] (f : frame_hom L M) :
  continuous_map (frame_hom M Prop) (frame_hom L Prop) :=
{ to_fun := λ p, frame_hom.comp p f,
  continuous_to_fun := begin
    rw continuous_def,
    rintros U ⟨a, rfl⟩,
    use f a,
    simp [frame_hom.comp_apply],
  end,
}

/--
This is a contravariant functor from `Frame` to `Top` which assigns each
frame to its frame of points and sends frame morphisms to postcomposition.
-/
@[simps]
def points : Frame.{u} ⥤ (Top.{u})ᵒᵖ :=
{ obj := λ L, opposite.op (bundled.of (frame_hom L Prop)),
  map := λ _ _ f, quiver.hom.op (pts_map f),
  map_id' := begin
    intros L,
    simp_rw [← op_id],
    congr,
    apply continuous_map.ext,
    intro p,
    rw [pts_map, Top.id_app, continuous_map.coe_mk],
    ext,
    simp,
  end,
  map_comp' := begin
    intros L M N f g,
    rw [← op_comp],
    congr,
  end,
}

/--
Given a frame `L`, sends each `a : L` to `{p | p a}`, the open set of points "contained" in `a`. 
-/
@[simps]
def points_opens_unit_map (L : Type u) [frame L] :
  frame_hom L (topological_space.opens (frame_hom L Prop)) :=
{ to_fun := λ a, ⟨{p | p a}, a, refl {p | p a}⟩,
  map_inf' := begin
    intros a b,
    simp_rw [map_inf],
    refl,
  end,
  map_top' := begin
    simp_rw [map_top],
    refl,
  end,
  map_Sup' := begin
    simp_rw [map_Sup, Sup_Prop_eq, set.mem_image, eq_iff_iff, exists_prop],
    intro as,
    ext p,
    split,
    { rintro ⟨prop, ⟨a, haas, hpaiffprop⟩, hprop⟩,
      cases eq_true_intro hprop,
      apply topological_space.opens.mem_Sup.mpr,
      use ⟨{q : frame_hom L Prop | q a}, a, refl {q | q a}⟩,
      split,
      { exact ⟨a, haas, refl _⟩},
      { exact hpaiffprop.mpr trivial, }},
    { intro h,
      obtain ⟨⟨U, a, rfl⟩, ⟨a', ha'as, h'⟩, hpa⟩ := topological_space.opens.mem_Sup.mp h,
      refine ⟨p a, ⟨a', ha'as, _⟩, hpa⟩,
      simp at h',
      exact (@set.ext_iff _ {q : frame_hom L Prop | q a'} {q | q a}).mp h' p }
  end,
}

lemma spatial_imp_points_opens_unit_map_injective {L : Type u} [frame L] [spatial L] :
  function.injective (points_opens_unit_map L) :=
begin
  intros a b h,
  by_contra,
  wlog h' : ¬ a ≤ b using [a b, b a],
  { simp_rw [←not_and_distrib],
    exact λ ⟨hab, hba⟩, h (le_antisymm hab hba), },
  obtain ⟨p, hpa, hnotpb⟩ := spatial.enough_points h',
  simp_rw [points_opens_unit_map, ←frame_hom.to_fun_eq_coe, subtype.mk_eq_mk, set.ext_iff] at h,
  exact hnotpb ((h p).mp hpa),
end

lemma points_opens_unit_map_surjective {L : Type u} [frame L] :
  function.surjective (points_opens_unit_map L) :=
begin
  rintro ⟨U, a, rfl⟩,
  use a,
  simp_rw [points_opens_unit_map, ←frame_hom.to_fun_eq_coe],
end

lemma spatial_imp_points_opens_unit_map_bijective {L : Type u} [frame L] [spatial L] :
  function.bijective (points_opens_unit_map L) :=
⟨spatial_imp_points_opens_unit_map_injective, points_opens_unit_map_surjective⟩

/--
Given a spatial frame `L`, sending `a : L` to the open `{p | p a}` of `frame_hom L Prop`
gives an order isomorphism.
-/
noncomputable def spatial_imp_points_opens_unit_map_order_iso (L : Type u) [frame L] [spatial L] :
  L ≃o topological_space.opens (frame_hom L Prop) :=
inf_hom.of_bijective spatial_imp_points_opens_unit_map_bijective

/--
A spatial frame `L` is isomorphic to `topological_space.opens (frame_hom L Prop))` in the
category of frames.
-/
noncomputable def spatial_imp_points_opens_unit_map_iso (L : Type u) [frame L] [spatial L] :
  (@bundled.of frame L _) ≅ (bundled.of (topological_space.opens (frame_hom L Prop))) :=
Frame.iso.mk (@spatial_imp_points_opens_unit_map_order_iso L _ _inst_2)

/--
The natural transformation with components given by `points_opens_unit_map`.
This is the unit of the Points ⊣ Opens adjunction.
-/
@[simps]
def points_opens_unit : 𝟭 Frame ⟶ points ⋙ Top_op_to_Frame :=
{ app := λ L, points_opens_unit_map L,
  naturality' := λ _ _ _, refl _,
}

/--
Given a tpological space `X`, sends each `x : X` to the localic point generated by `x`
(ie: the point which checks if an open `U` of `X` contains `x`).
-/
@[simps]
def points_opens_counit_map (X : Type u) [topological_space X] :
  continuous_map X (frame_hom (topological_space.opens X) Prop) :=
{ to_fun := λ x,
  { to_fun := λ U, x ∈ U,
    map_inf' := λ _ _, refl _, 
    map_top' := eq_true_intro (set.mem_univ x),
    map_Sup' := begin
      intro Us,
      simp_rw [topological_space.opens.mem_Sup],
      ext,
      split,
      { rintro ⟨U, hUUs, hxU⟩,
        exact ⟨x ∈ U, ⟨U, hUUs, refl _⟩, hxU⟩ },
      { rintro ⟨_, ⟨U, hUUs, rfl⟩, hxU⟩,
        exact ⟨U, hUUs, hxU⟩ }
    end
  },
  continuous_to_fun := begin
    rw continuous_def,
    rintros _ ⟨⟨U, hU⟩, rfl⟩,
    exact hU,
  end,
}

/--
The natural transformation with components given by the opposite of `points_opens_counit_map`.
This is the counit of the Points ⊣ Opens adjunction.
-/
@[simps]
def points_opens_counit : Top_op_to_Frame ⋙ points ⟶ 𝟭 (Topᵒᵖ) :=
{ app := λ Xop, (quiver.hom.op (points_opens_counit_map Xop.unop) :
    (opposite.op (bundled.of _)) ⟶ (opposite.op Xop.unop)), 
  naturality' := λ _ _ _, refl _, 
} 

/--
The Points ⊣ Opens adjunction.

Taking the points of a frame is left adjoint to taking opens of topological spaces.
-/
def points_opens_adjunction : points.{u} ⊣ Top_op_to_Frame.{u} :=
category_theory.adjunction.mk_of_unit_counit
{ unit := points_opens_unit,
  counit := points_opens_counit,
  left_triangle' := begin
    ext L,
    simp_rw [nat_trans.comp_app, whisker_right_app, points_map, functor.associator_hom_app,
      whisker_left_app, category.id_comp, nat_trans.id_app', points_opens_unit_app,
      points_opens_counit_app, ←op_comp, ←op_id_unop],
    congr,
    ext p a,
    refl,
  end,
  right_triangle' := begin 
    ext X ⟨U, hU⟩,
    refl,
  end,
}
