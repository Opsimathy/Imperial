
import tactic
import group_theory.subgroup.basic
import group_theory.quotient_group


/--/ This is my First Coursework and my attempt to prove the 
First Isomorphism Theorem. In Mathematical terms this is:
Let f:G → *H be a group homomorphism with Kernel K.
Then K normal subgroup of G and G/K ≅ Im f 
-/

/- Here we are defining G and H to be groups-/
variables {G H: Type} [group G][group H]

/- This is my definition of a group homomorphism, but this is also built into
lean so that is what will be used for the remaining code-/

class group_hom_1 (f : G → H): Prop :=
(map_mul' (a b : G) : f (a * b) = f a * f b)

namespace my_group_hom
variables {X Y: Type} [has_one Y]


-- We use notation `G →* H` for the type of group homs from `G` to `H`.

/-- We are defining the image of a group homomorphism, and showing 
 it is a subgroup of the target group. -/
definition im (f : G →* H) : subgroup H :=
{ carrier := {h : H | ∃ g : G, f g = h },
  one_mem' := begin simp, use 1, apply map_one, end,
  mul_mem' := begin simp, intros g h n m p q, use n*p,
  rw f.map_mul, rw m, rw q, end,
  inv_mem' := begin simp, intro m, use m⁻¹, apply map_inv, end,
}
/-- The image of a subgroup under a group homomorphism, as a subgroup. -/
definition map (f : G →* H) (K : subgroup G) : subgroup H :=
{ carrier := {h : H | ∃ g : G, g ∈ K ∧ f g = h },
  one_mem' := begin simp, use 1, split, apply K.one_mem,
  apply map_one, end,
  mul_mem' := begin simp, intros k g n m l p q r, use n*p,split, apply K.mul_mem,
  apply m, apply q, have h:= f.map_mul n p, rw h, rw l, rw r, end,
  inv_mem' := begin simp, intros n m, use n⁻¹, split, apply K.inv_mem, apply m,
  apply map_inv, end,
} 
/-- The preimage of a subgroup under a group homomorphism, as a subgroup. -/
definition comap (f : G →* H) (K : subgroup H) : subgroup G :=
{ carrier := {g : G | f g ∈ K },
  one_mem' := begin simp, apply K.one_mem, end,
  mul_mem' := begin simp,
  intros n m q r,
  have h:= f.map_mul n m,
  apply K.mul_mem,
  apply q,
  apply r,
  end,
  inv_mem' := begin 
  simp,
  end,
}
/- Here I am defining the kernel and showing it is a subgroup of G-/
definition ker_subgroup (f : G →* H): subgroup G :=
  {carrier := {g : G | f g = 1 },
  one_mem' := begin simp, end,
  mul_mem' := 
  begin 
  simp,
  intros j k m n,
  have h:= f.map_mul j k,
  rw m at h,
  rw n at h,
  norm_num at h,
  apply h,
  end,
  inv_mem' := begin simp,
  end,
}

/- Here is my structure definition of the normal subgroup which we use later on-/
structure normal (H : subgroup G): Prop :=
(conj_mem : ∀ (h:G), h ∈ H → ∀ (g : G), g * h * g⁻¹ ∈ H)

/- I'm now going to show that the Kernel is a Normal Subgroup-/

instance ker_normal_in (f : G →* H)(a : G)
 (k : ker_subgroup f):
(ker_subgroup f).normal :=
begin
have h1 := f.map_mul,
constructor,
intros l m n,
have h2 : f(n*l*n⁻¹) = f(n)*f(l)*f(n⁻¹),
rw h1,
rw h1,
have h3: f(n)*f(l)*f(n⁻¹) = 1,
have h4: f(l) = 1,
apply m,
rw h4,
simp,
have h5 : f(n*l*n⁻¹) = 1,
rw h2,
rw h3,
apply h5,
end
/- We've now shown the kernel subgroup is normal-/

/- Here are a few defintions below for injective and surjective -/

definition injective (f: G → H) : Prop :=
∀ (x:G)(y:G), (f(x)=f(y) → x=y)

definition surjective (f : G → H) : Prop :=
∀ (y:H), ∃ (x:G), f(x) = y

/- Here I've defined the trivial subgroup and shown it is indeed a subgroup-/
definition trivial_subgroup [group G]: subgroup G :=
{carrier := {x | x = 1 },
  one_mem' := begin simp, end,
  mul_mem' := begin simp,intros m n h j, rw h,rw j, simp, end,
  inv_mem' := begin simp, end,
}
/- Here are the definitons for left and right inverses-/
definition left_inv (g : Y → X)(f : X → Y) : Prop :=
∀ x, g (f x) = x

definition right_inv (g : Y → X)(f : X → Y) : Prop :=
∀ x, f (g x) = x

/- I then decided to prove that f is injectice iff the kernel subgroup is the 
trivial subgroup. I did this first from injective → kernel is trivial -/
lemma inj_then_kernel_eq_trivial (f: G →* H) (a x y :G)
(h : injective f) : ker_subgroup f = trivial_subgroup :=
begin
ext g,
split,
intro m,
have h1 : f(1)=1,
simp,
have h3: f(x)=f(y)→ x=y,
apply h,
have h4: f(g)=f(1)→ g=1,
intro p,
apply h,
apply p,
have h5: f(g)=1,
apply m,
have h6: f(g)=f(1),
rw h5,
simp,
have h7: g=1,
apply h4,
apply h6,
apply h7,
intro k,
have r: g=1,
apply k,
rw r,
have h1 : f(1)=1,
simp,
apply h1,
end 

/- Here is the proof that the kernel is trivial → f is injective -/

lemma kernel_eq_trivial_then_inj (f: G →* H) (x y :G)
(h : ∀(x y : G), (x*y⁻¹) ∈ ker_subgroup f ↔ x*y⁻¹ = 1) : injective f :=
begin 
  intros x y c,
  have h1 : f(x) = f(y) → f(x*y⁻¹) = 1,
  have h2 : f(x*y⁻¹)=f(x)*f(y⁻¹),
  apply f.map_mul,
  intro m,
  rw h2,
  rw m,
  rw f.map_inv,
  simp,
  have h3 : f(x*y⁻¹) =1 → x*y⁻¹=1,
  intro p,
  have h7 : x*y⁻¹ ∈ ker_subgroup f,
  apply p,
  rw ← h,
  apply h7,
  have h4 : x*y⁻¹=1 → x=y,
  have h6 : y⁻¹*y=1,
  rw inv_mul_self,
  have j: (x * y⁻¹) * y  = x * (y⁻¹*y),
  rw mul_assoc,
  rw h6 at j,
  intro k,
  rw k at j,
  simp at j,
  rw j,
  have h5 : f(x) = f(y) → x=y,
  intro s,
  rw ← h4,
  rw ← h3,
  rw ← h1,
  apply s,
  apply h5,
  apply c,
end

/- Here are my definitions for isomorphism and bijective-/
definition bijective (f: G → H ) :=
injective f ∧ surjective f

definition isomorphism (f: G → H) : Prop :=
bijective f ∧ group_hom_1 f

/- let N be a normal subgroup -/
variables (N : subgroup G) [subgroup.normal N]

/- the quotient group G/N is a group -/
example : group (G ⧸ N) := by apply_instance

/- the group homomorphism from `G` to `G ⧸ N` -/
example : G →* G ⧸ N := quotient_group.mk' N


/- With H and G as groups from before we define group hom `φ : G →* H` 
such that `g ∈ N → φ g = 1` -/

variables (φ : G →* H) (hφ : ∀ g, g ∈ N → φ g = 1)

/- In Lean instead of saying descends we say lifts and so
 The inbuilt homomorphism is `G ⧸ N → * H` -/
example : G ⧸ N →* H := quotient_group.lift N φ hφ

/- The diagram below shows how the mk' and the lift
 sits in the following commutative diagram which we can
 then stated below

     φ
  G ----> H
  |      /\
  |mk'  /
  |    / lift
  |   /
  \/ /
  G/N

-/

example (g : G) : (quotient_group.lift N φ hφ) (quotient_group.mk' N g) = φ g :=
quotient_group.lift_mk N hφ g 

/- Here is a proof that for all g in the kernel, φ(g) = 1 -/
lemma im_eq_one_of_mem_ker (φ : G →* H ) : ∀(g : G), g ∈ (ker_subgroup φ) →  φ(g) =1 :=
begin
  intros h j,
  apply j,
end 

end my_group_hom