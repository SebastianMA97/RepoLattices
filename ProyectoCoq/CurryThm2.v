From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.

Notation ρ := (reflexT _).
Notation τ := (transT _).
Notation σ := (antisymT _).

Lemma ΛK {T : lattice} (z : T) : forall a b : T ,  (a ⊓ b) ≤ a.
Proof.
move=> a b.
move: (ρ (a ⊓ b)).
by rewrite -(MH (a ⊓ b) a b) => /proj1.
Qed.

Lemma ΛK' {T : lattice} (z : T) : forall a b : T , (a ⊓ b) ≤ b.
Proof.
move=> a b.
move: (ρ (a ⊓ b)).
by rewrite -(MH (a ⊓ b) a b) => /proj2.
Qed.

Lemma ΛS {T : lattice} (z : T) : forall a b c : T , ((c ≤ a /\ c ≤ b) -> c ≤ (a ⊓ b)).
Proof.
move=> a b c.
by move: (MH c a b) => /proj1.
Qed.

Inductive STerm : Set := 
| svar : nat -> STerm
| sOp  : STerm -> STerm -> STerm.

Fixpoint evalS (sL : lattice) (z : sL) (env : seq sL) (t : STerm)  : sL :=
  match t with
  | svar n => nth z env n
  | sOp t1 t2 => evalS sL z env t1 ⊓ evalS sL z env t2
  end.

Inductive SForm : Set :=
| fs_leq  : STerm -> STerm -> SForm
| fs_eq   : STerm -> STerm -> SForm.

Fixpoint evalS_f (L : lattice) (z : L) (env : seq L) (f : SForm) : Prop :=
  match f with
  | fs_leq t1 t2 => (evalS L z env t1) ≤ (evalS L z env t2)
  | fs_eq t1 t2  => (evalS L z env t1) = (evalS L z env t2)
  end.

Definition Leq (s t : STerm) : Prop := forall L z env, evalS L z env s  ≤ evalS L z env t.

Definition Equiv (s t : STerm) : Prop := forall L z env, evalS L z env s = evalS L z env t.

Fixpoint atm_en (s : STerm) (j : nat) :=
  match s with
  | svar i => i = j
  | sOp s1 s2 => (atm_en s1 j) \/ (atm_en s2 j)
  end.

Fixpoint leq (s t : STerm) :=
  match t with
  | svar j => atm_en s j
  | sOp t1 t2 => (leq s t1) /\ (leq s t2)
  end.

Lemma atm_en_eval_le (sL : lattice) (z : sL) (env : seq sL) (s : STerm) j :
  atm_en s j -> evalS sL z env s ≤ nth z env j.
Proof.
elim s =>  [i|s1 H1 s2 H2] /=.
  move=> H.
  rewrite H.
  by move: (ρ (nth z env j)).
  move=> [H|H].
    move: (ΛK z (evalS sL z env s1) (evalS sL z env s2 ))=> Hle.
    apply (τ (evalS sL z env s1 ⊓ evalS sL z env s2) (evalS sL z env s1) _ ).
      by [].
    by move: H => /H1.
move: (ΛK' z (evalS sL z env s1) (evalS sL z env s2))=> Hle.
apply (τ (evalS sL z env s1 ⊓ evalS sL z env s2) (evalS sL z env s2) _ ).
  by [].
by move: H => /H2.
Qed.

Lemma leq_impl_Leq s t :
  leq s t -> Leq s t.
Proof.
elim: t => [j|t1 H1 t2 H2] /=.
  move=> H sL z env.
  rewrite {2}/evalS.
  by move: ((atm_en_eval_le sL z env s j) H).
move=> [Hs1 Hs2] sL0 z0 env0.
apply: (ΛS z0).
split.
  by apply: H1.
by apply: H2.
Qed.


Ltac rankS env n v :=
  match env with
  | (cons ?X1 ?X2) =>
      let env' := constr:(X2) in
        match constr:(X1 = v) with
        | (?X1 = ?X1) => n
        | _ => rankS env' (S n) v
        end
  end.

Ltac reflectS env m v :=
  match v with
  | (m _ ?X1 ?X2) =>
      let r1 := reflectS env m X1
      with r2 := reflectS env m X2 in
        constr:(sOp r1 r2)
  | ?X1 =>
      let n := rankS env 0 X1 in
        constr:(svar n)
  | _ => constr:(svar 0)
  end.

Ltac reflect_formS env m f :=
  lazymatch f with
  | ?x ≤ ?y =>
        let rx := reflectS env m x in
        let ry := reflectS env m y in
        constr:(fs_leq rx ry)
  | ?x = ?y =>
        let rx := reflectS env m x in
        let ry := reflectS env m y in
        constr:(fs_eq rx ry)
  | _ => fail "reflect_form: No reconozco esta forma:" f
  end.

Lemma reflectS_sound (L : lattice) (z : L) (env : seq L) (f : SForm) :
  evalS_f L z env f <-> evalS_f L z env f.
Proof. by []. Qed.

Ltac reflectS_goal z env m :=
  match goal with
  | |- ?G =>
      let FG := reflect_formS env m G in
      apply (proj1 (reflectS_sound _ z env FG))
  end.