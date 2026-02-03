import tactic -- imports all the Lean tactics
import algebra.category.Group.basic
import group_theory.coset
import data.zmod.basic
import data.fin.basic
import number_theory.zsqrtd.gaussian_int
import data.nat.parity
import data.zmod.parity


--------------------------------------------------
--  DEFIINTIONS
--  for cyctors, orthogonality, (cyclic) hadamard matrices
--  and some other helper definitions
-------------------------------------------------- 

/-- A cyctor is basically a finite direct product of a finite group -/
structure cyctor (G : Type) [add_group G] [decidable_eq G] (n : ℕ) :=    -- wait we do need divisibility... change "monoid"? -- ok have changed to group, but don't need identity
(to_vec : vector G n)
(is_finite : fintype G)

namespace cyctor

/-- negation is done element-wise -/
def neg {G : Type} [add_group G] [decidable_eq G] {n : ℕ} :
    (cyctor G n) → (cyctor G n) := 
begin
    intro c,
    use vector.map (λ (x : G), -x) (vector.of_fn (λ (x : fin n), c.to_vec.nth x)),
    use c.is_finite,
end

/-- addition is done element-wise -/
def add {G : Type} [add_group G] [decidable_eq G] {n : ℕ} :
    (cyctor G n) → (cyctor G n) → (cyctor G n) := 
begin
    intros c d,
    use vector.of_fn (λ (x : fin n), (c.to_vec.nth x) + (d.to_vec.nth x)),
    use c.is_finite,
end

/-- subtraction is done element-wise -/
def sub {G : Type} [add_group G] [decidable_eq G] {n : ℕ} :
    (cyctor G n) → (cyctor G n) → (cyctor G n)
| C := λ D, C.add D.neg

/-- the nil cyctor is the cyctor with an empty vector -/
def nil {G : Type} [add_group G] [decidable_eq G] (h : fintype G) :
    (cyctor G 0) := 
{
    to_vec := vector.nil,
    is_finite := h,
}

/-- the sum of all the elements in a cyctor -/
def sum {G : Type} [add_group G] [decidable_eq G] {n : ℕ} :
    (cyctor G n) → G
| C := C.to_vec.to_list.sum

/-- a kronecker product of elements in a cyctor 
for exmaple [3,4].product [2,5] = [5,8,6,9]-/
def product {G : Type} [add_group G] [decidable_eq G] {n m : ℕ} :
    cyctor G n → cyctor G m → cyctor G (n * m) :=
begin
    intros C D,
    let l : list (G × G) := C.to_vec.to_list.product D.to_vec.to_list,
    let v : vector (G × G) (n * m) :=
    ⟨
        l,
        begin
            rw list.length_product C.to_vec.to_list D.to_vec.to_list, 
            rw C.to_vec.to_list_length,
            rw D.to_vec.to_list_length,
        end
    ⟩,
    let E : cyctor G (n * m) :=
    {
        to_vec := vector.map (λ (a : G × G), a.1 + a.2) v,
        is_finite := C.is_finite
    },
    use E,
end

variables (n : ℕ) (G : Type) [add_group G] [decidable_eq G] (C : cyctor G n) (g : G)

instance : has_neg (cyctor G n) := ⟨neg⟩
instance : has_add (cyctor G n) := ⟨add⟩
instance : has_sub (cyctor G n) := ⟨sub⟩

-- I don't understand notation well enough to figure out why things go wrong
-- prefix `-`:20 := cyctor.neg
-- infixl ` + `:10 := cyctor.add
-- infixl ` - `:10 := cyctor.sub

end cyctor

/-- the cartesian product of two vectors -/
def vector.product {α β : Type} {h i : ℕ} :
    vector α h → vector β i → vector (α × β) (h*i) :=
begin
    intros U V,
    let Ulist := U.to_list,
    let Vlist := V.to_list,
    let Wlist := Ulist.product Vlist,
    use Wlist,
    rw list.length_product Ulist Vlist,
    rw U.to_list_length,
    rw V.to_list_length,
end

instance {G : Type} [add_group G] [decidable_eq G] {n : ℕ} : has_coe (cyctor G n) (vector G n) := 
{ coe := λ H, H.to_vec }

instance {G : Type} [add_group G] [decidable_eq G] {n : ℕ} : has_coe (vector G n) (list G) := 
{ coe := λ (v : vector G n), v.to_list }

/-- two cyctors are orthogonal if their difference contains
each member of G an equal number of times -/
def orthogonal {G : Type} [add_group G] [decidable_eq G] {n : ℕ} (C D : cyctor G n) : Prop :=
∀ (g h : G), list.count g (C.sub D) = list.count h (C.sub D)

/--
A general hadamard structure over an arbitrary additive group.
G is the underlying (additive) group
h is the height (number of pairwise orthogonal cyctors)
n is the length of each cyctor
-/
structure cyc_hadamard (G : Type) [add_group G] [decidable_eq G] (n h : ℕ) :=
(cyctors : vector (cyctor G n) h)
(pairwise_orthog : ∀ (i j : fin h), i ≠ j → orthogonal (cyctors.nth i) (cyctors.nth j))

def cyc_hadamard_exist (G : Type) [add_group G] [decidable_eq G] (n h: ℕ) :=
    nonempty(cyc_hadamard G n h)

/--
The definition of a Hadamard matrix
n is the order of the matrix
-/
structure hadamard (n : ℕ) := 
(cyctors : vector (cyctor (zmod 2) n) n)
(pairwise_orthog : ∀ (i j : fin n), i ≠ j → orthogonal (cyctors.nth i) (cyctors.nth j))

def hadamard_exist (n : ℕ) := nonempty(hadamard n)


--------------------------------------------------
--  BASIC PROPERTIES
--  transpose of hadamard matrix is hadamard matrix
--  orthogonality is symmetric
--------------------------------------------------

/-- it turns out that the transpose of a Hadamard matrix is also 
a Hadamard matrix, although a proof if this is quite finnicky -/
def hadamard.transpose {n : ℕ} (H : hadamard n) : hadamard n :=
begin
    cases H with H H_ortho,
    have f : (fin n) → cyctor (zmod 2) n,
    {
        intro k,
        let C : cyctor (zmod 2) n :=
        {
            to_vec := vector.of_fn (λ (m : fin n), (H.nth m).to_vec.nth k),
            is_finite := zmod.fintype 2
        },
        use C,
    },
    let V := vector.of_fn f,
    use V,
    
    -- now we need to prove this is actually a Hadamard matrix, but
    -- this is likely extremely hard to do in Lean, since it is 
    -- challenging even on paper (refer to the pdf for a proof)
    {
        sorry,
    }
end

/-- orthogonality between two cyctors is a symmetric relation -/
theorem orthogonal.is_symm {G : Type} [add_group G] [decidable_eq G] (n : ℕ) : is_symm (cyctor G n) orthogonal :=
begin
    split,
    intros a b aob,
    unfold orthogonal at *,
    intros g h,
    have hh := aob (-g) (-h),
    unfold cyctor.sub at *,
    unfold cyctor.add at *,
    unfold cyctor.neg at *,
    simp at *,
    unfold coe at *,
    unfold lift_t at *,
    unfold has_lift_t.lift at *,
    unfold coe_t at *,
    unfold has_coe_t.coe at *,
    unfold coe_b at *,
    unfold has_coe.coe at *,
    simp at *,
    rw ←list.count_map_of_injective (list.of_fn (λ _, _)) (λ (x : G), -x),
    {
        simp at *,
        unfold function.comp,
        simp at *,
        rw hh,
        rw ←list.count_map_of_injective (list.of_fn (λ _, _)) (λ (x : G), -x),
        simp,
        unfold function.comp,
        simp,
        {
            exact neg_injective,
        },
    },
    {
        exact neg_injective,
    },
end


--------------------------------------------------
--  HADAMARD MATRICES EXIST
--  for all orders that are powers of two
--  (in general they are conjectured to exist for all
--  multiples of four, as well as 1 and 2)
--------------------------------------------------

/-- two more than a natural number is not less than two -/
private lemma nat_succ_succ_not_lt_two (n : ℕ) : ¬(n.succ.succ < 2) :=
begin
    intro h,
    rw nat.succ_lt_succ_iff at h,
    rw nat.succ_lt_succ_iff at h,
    exact nat.not_lt_zero n h,
end

-- I thought about using induction with two base cases, but eventually
-- I found a faster way to prove he2
private lemma two_base_induction (p : ℕ → Prop) (n : ℕ) : (p 0) ∧ (p 1) ∧ (∀ n, (n > 1 → p n)) ↔ (∀ n, p n) :=
begin
    split,
    {
        intro p,
        cases p with p0 p1,
        cases p1 with p1 p2,
        intro n,
        induction n,
        {
            exact p0,
        },
        {
            induction n_n,
            {
                exact p1,
            },
            {
                apply p2,
                exact nat.one_lt_succ_succ n_n_n,
            }
        }
    },
    {
        intro pn,
        split,
        {
            exact pn 0,
        },
        {
            split,
            {
                exact pn 1,
            },
            {
                intros n n1,
                exact pn n,
            }
        }
    }
end

/-- if k is in fin 2, then it is either 0 or 1-/
private lemma le_two_is_zero_or_one_fin (k : fin 2) : (k = (0 : fin 2) ∨ k = (1 : fin 2)) :=
begin
    cases k with k1 k2,
    induction k1 with k ks,
    {
        left,
        simp,
    },
    {
        induction k with k ks,
        {
            right,
            simp,
        },
        {
            by_contra hh,
            apply nat_succ_succ_not_lt_two k,
            exact k2,
        }
    }
end

/-- we can prove n = m by proving they're both equal to some intermediary -/
private lemma eq_transi (n m : ℕ) : (∃ (k : ℕ), (n = k) ∧ (m = k)) ↔ n = m :=
begin
    exact exists_eq_right',
end

/-- A hadamard matrix of order 1 exists -/
theorem he1 : hadamard_exist 1 :=
begin
    unfold hadamard_exist,
    split,
    let C : cyctor (zmod 2) 1 :=
    {
        to_vec := begin use([0]), refl end,
        is_finite := zmod.fintype 2
    },
    use ([C]),
    { refl, },
    {
        intros i j inej,
        cases i with inat ile1,
        cases j with jnat jle1,
        rw nat.lt_one_iff at ile1,
        rw nat.lt_one_iff at jle1,
        simp at inej,
        rw [ile1, jle1] at inej,
        contradiction,
    }
end

/-- A helper lemma to prove a Hadamard matrix of order two exists -/
private lemma he2_aux₁
(C : cyctor (zmod 2) 2)
(D : cyctor (zmod 2) 2)
{a b : fin 2}
(g : zmod 2)
(i0 : a = 0)
(j1 : b = 1) :
(C = {to_vec := begin use ([0, 0]), refl end, is_finite := zmod.fintype 2}) → (D = {to_vec := begin use ([0, 1]), refl end, is_finite := zmod.fintype 2}) →
list.count g ↑((vector.nth ⟨[C, D], begin refl end⟩ a).sub (vector.nth ⟨[C, D], begin refl end⟩ b)) = 1 :=
begin
    intros Cis Dis,
    rw [i0,j1],
    cases g with g gle2,
    induction g with g gs,
    {
        rw Cis,
        rw Dis,
        refl,
    },
    {
        induction g with g g2,
        {
            rw Cis,
            rw Dis,
            refl,
        },
        {
            by_contra,
            apply nat_succ_succ_not_lt_two g gle2,
        }
    }
end

/-- Another helper lemma to prove a Hadamard matrix of order two exists -/
private lemma he2_aux₂
(C : cyctor (zmod 2) 2)
(D : cyctor (zmod 2) 2)
{a b : fin 2}
(g : zmod 2)
(i0 : a = 0)
(j1 : b = 1) :
(C = {to_vec := begin use ([0, 0]), refl end, is_finite := zmod.fintype 2}) → (D = {to_vec := begin use ([0, 1]), refl end, is_finite := zmod.fintype 2}) →
list.count g ↑((vector.nth ⟨[C, D], begin refl end⟩ b).sub (vector.nth ⟨[C, D], begin refl end⟩ a)) = 1 :=
begin
    intros Cis Dis,
    rw [i0,j1],
    cases g with g gle2,
    induction g with g gs,
    {
        rw Cis,
        rw Dis,
        refl,
    },
    {
        induction g with g g2,
        {
            rw Cis,
            rw Dis,
            refl,
        },
        {
            by_contra,
            apply nat_succ_succ_not_lt_two g gle2,
        }
    }
end

/-- Finally, a hadamard matrix of order two exists -/
theorem he2 : hadamard_exist 2 :=
begin
    unfold hadamard_exist,
    split,
    {
        -- First, we define the vectors we're going to use
        let C : cyctor (zmod 2) 2 :=
        {
            to_vec := begin use ([0,0]), refl end,
            is_finite := zmod.fintype 2,
        },
        let D : cyctor (zmod 2) 2 :=
        {
            to_vec := begin use ([0,1]), refl end,
            is_finite := zmod.fintype 2,
        },
        let Ch : C = {
            to_vec := begin use ([0,0]), refl end,
            is_finite := zmod.fintype 2,
        },
        {
            rw eq_self_iff_true,
            triv,
        },
        let Dh : D = {
            to_vec := begin use ([0,1]), refl end,
            is_finite := zmod.fintype 2,
        },
        {
            rw eq_self_iff_true,
            triv,
        },
        -- We construct the Hadamard matrix
        use ([C, D]),
        {
            refl,
        },
        {   
            -- We prove the two rows are orthogonal.
            -- A huge bash ensues...
            -- we could have used the fact that orthogonality
            -- is symmetric, but I ran out of time to make the change
            intros i j inej,
            unfold orthogonal,
            intros g h,
            rw ←eq_transi _ _,
            use 1,
            split,
            {
                have i01 := le_two_is_zero_or_one_fin i,
                have j01 := le_two_is_zero_or_one_fin j,
                cases i01 with i0 i1,
                {
                    cases j01 with j0 j1,
                    {
                        rw [i0, j0] at inej,
                        contradiction,
                    },
                    {
                        exact he2_aux₁ C D g i0 j1 Ch Dh,
                    }
                },
                {
                    cases j01 with j0 j1,
                    {

                        exact he2_aux₂ C D g j0 i1 Ch Dh,
                    },
                    {
                        rw [i1, j1] at inej,
                        contradiction,
                    },
                }
            },
            {
                have i01 := le_two_is_zero_or_one_fin i,
                have j01 := le_two_is_zero_or_one_fin j,
                cases i01 with i0 i1,
                {
                    cases j01 with j0 j1,
                    {
                        rw [i0, j0] at inej,
                        contradiction,
                    },
                    {
                        exact he2_aux₁ C D h i0 j1 Ch Dh,
                    }
                },
                {
                    cases j01 with j0 j1,
                    {
                        exact he2_aux₂ C D h j0 i1 Ch Dh,
                    },
                    {
                        rw [i1, j1] at inej,
                        contradiction,
                    },
                }
            }
        }
    }
end

/-- If a cyclic hadamard matrix over G exists for n × h_n and m × h_m, 
the it exists for (nm) × (h_n h_m) via a kronecker product construction -/
theorem cyc_hadamard_mul {G : Type} [add_group G] [decidable_eq G] {n h_n m h_m : ℕ} :
    cyc_hadamard_exist G n h_n → cyc_hadamard_exist G m h_m → cyc_hadamard_exist G (n*m) (h_n*h_m):=
begin
    intros hn hm,
    unfold cyc_hadamard_exist at *,
    cases hn with N,
    cases hm with M,
    cases N with N N_ortho,
    cases M with M M_ortho,
    split,
    let V := N.product M,
    let W := vector.map (λ (a : cyctor G n × cyctor G m), a.1.product a.2) V ,
    use W,
    intros i j inej,
    unfold orthogonal,
    intros g h,
    -- this is going to be tedious, but at least we've defined the matrix
    -- there are two cases to consider: when i = j mod h_m, and when not
    sorry,
end

/-- a Hadamard matrix is an instance of a cyclic Hadamard matrix
I'm not sure how to use "instance" to achieve this effect -/
theorem hadamard_cyc_hadamard_eq (n : ℕ) : hadamard_exist n ↔ cyc_hadamard_exist (zmod 2) n n :=
begin
    split,
    {
        unfold hadamard_exist,
        unfold cyc_hadamard_exist,
        rw nonempty.forall,
        intro hen,
        split,
        cases hen with hen hen_ortho,
        use hen,
        exact hen_ortho,
    },
    {
        unfold hadamard_exist,
        unfold cyc_hadamard_exist,
        rw nonempty.forall,
        intro ch,
        split,
        cases ch with ch ch_ortho,
        use ch,
        exact ch_ortho,
    },
end

/-- Hadamard matrices exist for all orders that are powers of two -/
theorem hadamard_exists_for_powers_of_two : ∀ (n : ℕ), hadamard_exist (2 ^ n) :=
begin
    intro n,
    induction n,
    { exact he1, },
    {
        have ch2 := he2,
        rw hadamard_cyc_hadamard_eq at *,
        have h := cyc_hadamard_mul n_ih ch2,
        change cyc_hadamard_exist (zmod 2) (2 ^ (n_n + 1)) (2 ^ (n_n + 1)),
        rw pow_succ',
        exact h,
    }
end


--------------------------------------------------
--  HADAMARD MATRICES DON'T EXIST
--  for non-multiples of 4
--  (except 1 and 2)
--------------------------------------------------

/-- This lemma says that if two predicates are equal, the quantities of things
they count in any list are the same -/
private lemma p_iff_q_imp_countp_eq {α : Type} (p q : α → Prop) [decidable_pred p] [decidable_pred q] (l : list α) :
    (p = q) → list.countp p l = list.countp q l :=
begin
    intro h,
    simp_rw h,
    congr',
end

/-- This lemma says that the quantities of 0's and 1's in a zmod 2 list
sum to the length of the list -/
private lemma list_zmod_two_count (l : list (zmod 2)) : l.count (0 : zmod 2) + l.count (1 : zmod 2) = l.length :=
begin
    unfold list.count,
    change list.countp (eq 0) l + list.countp (eq 1) l = l.length,
    have h := list.length_eq_countp_add_countp (eq (0 : zmod 2)),
    specialize h l,
    rw h,
    simp,
    apply p_iff_q_imp_countp_eq,
    ext,
    split,
    {
        intro x1,
        rw ←x1,
        simp,
    },
    {
        intro xn0,
        have hh : x = 0 ∨ x = 1,
        {
            exact le_two_is_zero_or_one_fin x
        },
        cases hh,
        {
            exfalso,
            exact xn0 (eq.symm hh),
        },
        { exact eq.symm hh, },  
    },
end

/-- Hadamard matrices don't exist for odd orders greater than one -/
theorem hadamard_empty_for_odd_ge_one : ∀ (n : ℕ), odd n → n > 1 → ¬hadamard_exist n :=
begin
    intros n nisodd nge1 hen,
    unfold hadamard_exist at hen,
    have hn := hen.some,
    cases hn with hn hn_ortho,
    unfold orthogonal at hn_ortho,
    let zero : fin n := ⟨0, by linarith⟩,
    let one : fin n := ⟨1, by linarith⟩,
    have zeroisnotone : zero ≠ one := by simp,
    specialize hn_ortho zero one zeroisnotone 0 1,
    simp at hn_ortho,
    change list.count 0 ((hn.nth zero).sub (hn.nth one)).to_vec.to_list =
        list.count 1 ((hn.nth zero).sub (hn.nth one)).to_vec.to_list at hn_ortho,
    have h : list.count 0 ((hn.nth zero).sub (hn.nth one)).to_vec.to_list +
        list.count 1 ((hn.nth zero).sub (hn.nth one)).to_vec.to_list = n,
    {
        have list_zmod_two_count :=
            list_zmod_two_count ((hn.nth zero).sub (hn.nth one)).to_vec.to_list,
        rw list_zmod_two_count,
        simp,
    },
    rw hn_ortho at h,
    rw ←mul_two at h,
    have niseven : even n,
    {
        have inter : n % 2 = 0,
        {
            rw ←h,
            simp,
        },
        rw ←nat.even_iff at inter,
        exact inter,
    },
    rw nat.odd_iff_not_even at nisodd,
    contradiction,
end

lemma cyctor_sum_neg_commute {G : Type} [add_group G] [decidable_eq G] {n : ℕ} (C : cyctor G n):
    C.neg.sum = -(C.sum) :=
begin
    sorry,
end

lemma cyctor_sum_distrib_add {G : Type} [add_group G] [decidable_eq G] {n : ℕ} (C D : cyctor G n):
    (C.add D).sum = C.sum + D.sum :=
begin
    sorry,
end


theorem hadamard_empty_for_singly_even_ge_two : ∀ (n : ℕ), n % 4 = 2 → n > 2 → ¬hadamard_exist n :=
begin
    intros n n_singly_even nge2 hexist,
    unfold hadamard_exist at hexist,
    have hen := hexist.some,
    cases hen with hn hn_ortho,

    -- the main idea we will use is that the sum of a.sub b for 
    -- any two cyctors must be odd. But then if we have three
    -- cyctors a, b, and c, then the sum of their differences 
    -- cannot all be odd
    let zero : fin n := ⟨0, by linarith⟩,
    let one : fin n := ⟨1, by linarith⟩,
    let two : fin n := ⟨2, by linarith⟩,
    unfold orthogonal at hn_ortho,
    have h01 := hn_ortho zero one,
    have h12 := hn_ortho one two,
    have h20 := hn_ortho two zero,
    simp at *,
    specialize h01 0 1,
    specialize h12 0 1,
    specialize h20 0 1,
    sorry,
    -- this is all I had time to do
end

--------------------------------------------------
--  THE PALEY CONSTRUCTION
--  For constructing (from scratch) hadamard matrices
--  whenever (p^k)+1 or 2*((p^k)+1) is a multiple of four
--  (where p is prime)
--------------------------------------------------

/-- A helper definition for the next theorem, wihch I couldn't get to work -/
def paley_cons_qr : ℕ → ℕ → ℕ → zmod 2 :=
begin
    intros n i j,
    -- not sure how to get this function to work, it claims to require decidability
    -- let k : zmod 2 := if i = 0 ∨ j = 0 ∨ ¬(∃ (a : zmod n), ((a^2) - (i+j+2)) = (0 : zmod n)) then 1 else 0,
    -- use k,
    sorry,
end

/-- One basic Paley construction.  There are other more intricate constructions 
which cover more cases -/
lemma paley_construction_1a : ∀ (n : ℕ), n % 4 = 3 → prime n → hadamard_exist n :=
begin
    -- This construction can be done via quadratic residues
    intros n n43 nprime,
    sorry,
end

/-- This is the full Paley construction -/
theorem paley_construction : ∀ (n : ℕ), (∃ (p k : ℕ), (prime p) ∧
    ((p^k + 1 = n) ∨ (2 * (p^k + 1) = n))) → (n % 4 = 0) → hadamard_exist n :=
begin
    sorry,
end