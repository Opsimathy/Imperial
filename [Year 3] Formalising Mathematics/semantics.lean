import formula

/- The soundness and completeness theorems are always proven with respect to a 
semantics. In this file we define the usual truth-value based reasoning 
system, where formulas are evaluated to the truth value they denote. The 
evaluation is based on what truth values are assigned to the variables, so a
semantic model of propositional logic in this system is a truth assignment 
function to the propositional variables. We also define some related notions 
such as satisfiability.
-/

variable {vars : Type}

/-- Evaluates formulas to truth values given a propositional variable 
    truth assignment `v`. -/
def eval (v : vars → bool) : Form vars → bool
| ⊥       := ff
| ⦃x⦄     := v x
| (~ P)   := not (eval P)
| (P ⋀ Q) := and (eval P) (eval Q)
| (P ⋁ Q) := or (eval P) (eval Q)

notation `⟦` P `⟧_` v := eval v P
notation v ` ⊨ ` A := ⟦A⟧_v
notation v ` ⊨ ` Γ := ∀ γ, γ ∈ Γ → ⟦γ⟧_v

theorem no_bot (v : vars → bool) : ¬ (↥(v ⊨ ⊥)) :=
by simp [eval]

/-- A set of formulas Γ semantically entail another formula A iff 
all the models of Γ are models of A. -/
def entail (Γ : set (Form vars)) (A : Form vars) : Prop :=
∀ (v : vars → bool), (v ⊨ Γ) → (v ⊨ A)

notation Γ ` ⊨ ` A := entail Γ A
notation Γ ` ⊭ ` A := ¬ entail Γ A

/-- A set of formulas are satisfiable iff it has a model. -/
def satisfiable (Γ : set (Form vars)) : Prop :=
∃ (v : vars → bool), v ⊨ Γ

/-- A set of formulas are satisfiable iff it has no model. -/
def unsatisfiable (Γ : set (Form vars)) : Prop :=
¬ satisfiable Γ

variable {Γ : set (Form vars)}

theorem satisfiable_iff : satisfiable Γ ↔ (Γ ⊭ ⊥) :=
by simp [satisfiable, entail, eval]

theorem unsatisfiable_iff : unsatisfiable Γ ↔ (Γ ⊨ ⊥) :=
by simp [unsatisfiable, satisfiable_iff]

#lint