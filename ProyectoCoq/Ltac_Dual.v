From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.
From ProyectoCoq Require Import Dualidad.

Ltac rank env n v :=
  match env with
  | (cons ?X1 ?X2) =>
      let env' := constr:(X2) in
        match constr:(X1 = v) with
        | (?X1 = ?X1) => n
        | _ => rank env' (S n) v
        end
  end.

Ltac reflect env m j v :=
  match v with
  | (m _ ?X1 ?X2) =>
      let r1 := reflect env m j X1
      with r2 := reflect env m j X2 in
        constr:(Meet r1 r2)
  | (j _ ?X1 ?X2) =>
      let r1 := reflect env m j X1
      with r2 := reflect env m j X2 in
        constr:(Join r1 r2)
  | ?X1 =>
      let n := rank env 0 X1 in
        constr:(Var n)
  | _ => constr:(Var 0)
  end.

Ltac reflect_form env m j f :=
  lazymatch f with
  | ?x ≤ ?y =>
        let rx := reflect env m j x in
        let ry := reflect env m j y in
        constr:(f_leq rx ry)
  | ?x = ?y =>
        let rx := reflect env m j x in
        let ry := reflect env m j y in
        constr:(f_eq rx ry)
  | ~ ?p =>
        let rp := reflect_form env m j p in
        constr:(f_neg rp)
  | ?p /\ ?q =>
        let rp := reflect_form env m j p in
        let rq := reflect_form env m j q in
        constr:(f_conj rp rq)
  | ?p \/ ?q =>
        let rp := reflect_form env m j p in
        let rq := reflect_form env m j q in
        constr:(f_or rp rq)
  | ?p -> ?q =>
        let rp := reflect_form env m j p in
        let rq := reflect_form env m j q in
        constr:(f_imp rp rq)
  | _ => fail "reflect_form: No reconozco esta forma:" f
  end.

Lemma reflect_sound_full (L : lattice) (z : L) (env : seq L) (f : Form) :
  eval_f L z env f <-> eval_f L z env f.
Proof. by []. Qed.

Ltac reflect_goal z env m j :=
  match goal with
  | |- ?G =>
      let FG := reflect_form env m j G in
      apply (proj1 (reflect_sound_full _ z env FG))
  end.

Lemma reflectDual (L : lattice) (z : L) (env : seq L) (F : Form) : Teorema (F) -> eval_f L z env F.
Proof.
rewrite /Teorema=> H.
by move: (H L z env).
Qed.