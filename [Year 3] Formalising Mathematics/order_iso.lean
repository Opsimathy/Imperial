import order.hom.lattice

universes u v

namespace inf_hom

lemma semilattice_inf_hom_imp_monotone {α : Type u} {β : Type v}
  [semilattice_inf α] [semilattice_inf β] (f : inf_hom α β) :
  monotone f :=
begin
  intros a b,
  rw [←inf_eq_left, ←inf_eq_left],
  intro h,
  rw [←map_inf, h],
end 

/--
A bijective morphism of meet-semilattices gives rise to an order isomorphism.

The ordering of a meet-semilattice can be recovered from its meets, and these meets are
preserved by the morphism, so the inverse to the morphism will also respect the given ordering.
-/
noncomputable def of_bijective {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β]
  {f : inf_hom α β} (hf : function.bijective f) : α ≃o β :=
{ to_equiv := equiv.of_bijective _ hf,
  map_rel_iff' := begin
    intros a b,
    simp_rw [equiv.of_bijective_apply, ←inf_eq_left,  ←map_inf],
    exact function.injective.eq_iff hf.1,
  end
}

end inf_hom