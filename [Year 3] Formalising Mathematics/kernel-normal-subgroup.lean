import tactic
import group_theory.subgroup.basic

namespace my_kernel_norm_sub

variables {G H : Type} [group G] [group H]

lemma map_mul_2 {x y : G}{φ : G →* H} : φ(x * y * x⁻¹) = φ(x) * φ(y) * φ(x)⁻¹ :=
begin
    -- rewrite twice to get an obvious identiy
  rw map_mul,
  rw map_mul,
end

lemma x_in_kernel_is_identity {k : G}{φ : G →* H}(hk : k ∈ φ.ker) : φ(k) = 1 :=
begin
  exact hk,
end

lemma conjugating_k_in_kernel_by_x_is_identity
  {k : G}{φ : G →* H}(hk : k ∈ φ.ker){x : G} : φ(x * k * x⁻¹) = 1 :=
begin
  -- rewrite our hypothesis to expand to multiplication by function
  rw map_mul_2,
  -- kernel element goes to the identity
  rw x_in_kernel_is_identity hk,
  -- Remove the multiplication by 1
  rw mul_one,
  -- bring back the multiplication by maps to multiplication within a map
  rw ← map_mul,
  -- cancel x * x⁻¹
  rw mul_right_inv,
  -- identity maps to identity
  rw map_one,
end

variable {φ : G →* H}
lemma conjugating_kernel_by_x_is_in_kernel
  {k : G}(hk : k ∈ φ.ker){x : G} : x * k * x⁻¹ ∈ φ.ker :=
begin
    apply conjugating_k_in_kernel_by_x_is_identity,
    exact hk,
end

theorem kernel_is_normal_subgroup_of_domain {φ : G →* H} : subgroup.normal (φ.ker) :=
begin
  -- Change the goal to be the hypothesis of what a normal group is
  apply subgroup.normal.mk,
  apply conjugating_kernel_by_x_is_in_kernel,
end

theorem preimage_of_normal_subgroup_is_normal
  {φ : G →* H} {I : subgroup H}(hn : subgroup.normal(I)) :
    subgroup.normal (I.comap φ) :=
begin
  -- Change the goal to be the hypothesis of what a normal group is
  apply subgroup.normal.mk,
  -- y an element of G
  intro y,
  -- hypothesis that y is in the preimage of φ
  intro hyInPreim,
  -- x any element of G
  intro x,
  --Simplifies the goal from x * y * x⁻¹ ∈ subgroup.comap φ I
  -- to φ(x) * φ(y) * φ(x)⁻¹ ∈ I,
  simp,
  -- Apply the conjecture that the image I is a normal subgroup
  apply hn.conj_mem,
  -- φ(y) is in the image, thus proving the claim
  exact hyInPreim,
end

end my_kernel_norm_sub
