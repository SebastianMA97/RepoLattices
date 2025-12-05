From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.

Definition dord {T : ordenParcial} (x y : T) := ord T y x.

Lemma Dreflex {T : ordenParcial} : reflexive (@dord T).
Proof.
move: (reflexT T).
by rewrite /reflexive /dord.
Qed.

Lemma Dantisym {T : ordenParcial} : antisymetric (@dord T).
Proof.
move: (antisymT T).
rewrite /antisymetric /dord.
move=> H x y H0 H1.
by move: (H x y H1 H0).
Qed.

Lemma Dtrans {T : ordenParcial} : transitive (@dord T).
Proof.
move: (transT T).
rewrite /transitive /dord.
move=> H x y z H0 H1.
by move: (H z y x H1 H0).
Qed.

Canonical Structure dual_ord T := OrdenParcial (O T) (dord) Dreflex Dantisym Dtrans.

Canonical Structure dual_lattice_of (L : lattice) : lattice :=
  Lattice
    (dual_ord L) (meetT L) (fun z x y => mHT L z x y) (joinT L) (fun z x y => jHT L z x y).

Inductive Term : Set :=
| Var  : nat -> Term
| Meet : Term -> Term -> Term
| Join : Term -> Term -> Term.

Fixpoint eval (L : lattice) (z : L) (env : seq L) (t : Term) : L :=
  match t with
  | Var n     => nth z env n
  | Meet t1 t2 => @meetT L (eval L z env t1) (eval L z env t2)
  | Join t1 t2 => @joinT L (eval L z env t1) (eval L z env t2)
  end.

Inductive Form : Set :=
| f_leq  : Term -> Term -> Form
| f_eq   : Term -> Term -> Form
| f_neg  : Form -> Form
| f_conj : Form -> Form -> Form
| f_or   : Form -> Form -> Form
| f_imp  : Form -> Form -> Form.

Fixpoint eval_f (L : lattice) (z : L) (env : seq L) (f : Form) : Prop :=
  match f with
  | f_leq t1 t2 => (eval L z env t1) ≤ (eval L z env t2)
  | f_eq t1 t2  => (eval L z env t1) = (eval L z env t2)
  | f_neg f1     => ~ (eval_f L z env f1)
  | f_conj f1 f2  => eval_f L z env f1 /\ eval_f L z env f2
  | f_or f1 f2    => (eval_f L z env f1) \/ (eval_f L z env f2)
  | f_imp f1 f2   =>  (eval_f L z env f1) -> (eval_f L z env f2)
  end.

Fixpoint dual_t (t : Term) : Term :=
  match t with
  | Var n => Var n
  | Meet t1 t2 => Join (dual_t t1) (dual_t t2)
  | Join t1 t2 => Meet (dual_t t1) (dual_t t2)
  end.

Fixpoint dual (f : Form) : Form :=
  match f with
  | f_leq t1 t2 => f_leq (dual_t t2) (dual_t t1)
  | f_eq t1 t2  => f_eq (dual_t t1) (dual_t t2)
  | f_neg f1     => f_neg (dual f1)
  | f_conj f1 f2  => f_conj (dual f1) (dual f2)
  | f_or f1 f2    => f_or (dual f1) (dual f2)
  | f_imp f1 f2   => f_imp (dual f1) (dual f2)
  end.

(* Theorem eval_dual *)

Lemma jldm : forall (L : lattice), joinT (dual_lattice_of L) = meetT L.
Proof.
  by [].
Qed.

Lemma mldj : forall (L : lattice), meetT (dual_lattice_of L) = joinT L.
Proof.
  by [].
Qed.

Lemma  eval_m : forall (L : lattice) (z : L) (env : seq L) (t0 t1 : Term), 
              eval L z env (Meet t0 t1) = meetT L (eval L z env t0) (eval L z env t1).
Proof. by move=> L0 env0; rewrite /eval. Qed.

Lemma eval_j : forall (L : lattice) (z : L) (env : seq L) (t0 t1 : Term), 
              eval L z env (Join t0 t1) = joinT L (eval L z env t0) (eval L z env t1).
Proof. by move=> L0 env0; rewrite /eval. Qed.

Lemma eval_conj : forall (L : lattice) (z : L) (env : seq L) (f0 f1 : Form), 
                   eval_f L z env (f_conj f0 f1) = and (eval_f L z env f0) (eval_f L z env f1).
Proof.  by []. Qed.

Lemma dual_conj : forall (f0 f1 : Form), dual (f_conj f0 f1) = f_conj (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma eval_or : forall (L : lattice) (z : L) (env : seq L) (f0 f1 : Form), 
                   eval_f L z env (f_or f0 f1) = or (eval_f L z env f0) (eval_f L z env f1).
Proof.  by []. Qed.

Lemma dual_or : forall (f0 f1 : Form), dual (f_or f0 f1) = f_or (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma eval_imp : forall (L : lattice) (z : L) (env : seq L) (f0 f1 : Form), 
                   eval_f L z env (f_imp f0 f1) =(( eval_f L z env f0) -> (eval_f L z env f1)).
Proof. by []. Qed.

Lemma dual_imp : forall (f0 f1 : Form), dual (f_imp f0 f1) = f_imp (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma dual_m : forall t0 t1 : Term, 
                dual_t (Meet t0 t1) = Join (dual_t t0) (dual_t t1).
Proof.  by move=> t2 t3; rewrite /dual_t. Qed.

Lemma dual_j : forall t0 t1 : Term, 
                dual_t (Join t0 t1) = Meet (dual_t t0) (dual_t t1).
Proof.  by move=> t2 t3; rewrite /dual_t. Qed.

Lemma le_dual (L : lattice) (x y : L) :
  (ord (dual_lattice_of L) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Theorem eval_dual (L : lattice) (z : L) (env : seq L) (t : Term) :
  eval (dual_lattice_of L) z env t = eval L z env (dual_t t).
Proof.
elim t.
  
  (* Var n *)
  move=> n0.
  by rewrite  {1}/eval/dual_t/eval.
  
  (* Meet t0 t1*)
  move=> t0 H0 t1 H1.
  rewrite dual_m (eval_j L z env).
  rewrite (eval_m (dual_lattice_of L) z env).
  by rewrite H0 H1 mldj.

  (* Join t0 t1 *)
  move=> t0 H0 t1 H1.
  rewrite dual_j (eval_m L z env).
  rewrite (eval_j (dual_lattice_of L) z env).
  by rewrite H0 H1 jldm.
Qed.

Theorem eval_dual_f (L : lattice) (z : L) (env : seq L) (f : Form) :
  eval_f (dual_lattice_of L) z env f = eval_f L z env (dual f).
Proof.
elim f.
  (* Term *)
  move=> t0 t1.
  by rewrite /dual /eval_f eval_dual eval_dual.
  
  move=> t0 t1.
  by rewrite /dual /eval_f eval_dual eval_dual.
  
  (* Neg *)
  move=> f0 H0.
  have aux: forall (L : lattice) (z : L) (env : seq L) (f0 : Form), eval_f L z env (f_neg f0) = ~ (eval_f L z env f0).
    by [].
  have auxd: forall (f0 : Form), dual (f_neg f0) = f_neg (dual f0).
    by [].
  rewrite auxd aux aux.
  by rewrite H0.

  (* Conj *)
  move=> f0 H0 f1 H1.
  rewrite dual_conj eval_conj eval_conj.
  by rewrite H0 H1.
  
  (* Or *)
  move=> f0 H0 f1 H1.
  rewrite dual_or eval_or eval_or.
  by rewrite H0 H1.
  
  (* Imp *)
  move=> f0 H0 f1 H1.
  rewrite dual_imp eval_imp eval_imp.
  by rewrite H0 H1.
Qed.


Lemma dual_td : forall t : Term, t = dual_t (dual_t t).
Proof.
move=> t; elim t.
  by rewrite /dual_t.
  
  move=> t0 H0 t1 H1.
  by rewrite dual_m dual_j -H0 -H1.
  
  move=> t0 H0 t1 H1.
  by rewrite dual_j dual_m -H0 -H1.
Qed.

Lemma duald : forall F : Form, F = dual (dual F).
Proof.
move=>F; elim F.
  by move=> t0 t1; rewrite /dual {1}(dual_td t0) {1}(dual_td t1).

  by move=> t0 t1; rewrite /dual {1}(dual_td t0) {1}(dual_td t1).

  by move=> F0 H0; rewrite {1}H0 {3 4}/dual.

  by move=> F0 H0 F1 H1; rewrite dual_conj dual_conj -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dual_or dual_or -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dual_imp dual_imp -H0 -H1.
Qed.

Definition Teorema (F : Form) : Prop :=
forall (L : lattice) (z : L) (env : seq L), (eval_f L z env F).

Theorem Dualidad : forall f : Form, (Teorema f) -> (Teorema (dual f)).
Proof.
move=> f.
elim f.
  move=> t0 t1.

    (* Caso: leq *)

    rewrite /dual /Teorema => Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    by rewrite eval_dual_f /dual.

    (* Caso: eq *)
    
    rewrite /Teorema /dual /eval_f => t0 t1 Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    by rewrite eval_dual eval_dual.

    (* Caso: neg *)
    rewrite /Teorema => f0 _ Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    have aux: forall (L : lattice) (z : L) (env : seq L) (f0 : Form), eval_f L z env (f_neg f0) = ~ (eval_f L z env f0).
      by [].
    have auxd: forall (f0 : Form), dual (f_neg f0) = f_neg (dual f0).
      by [].
    rewrite auxd aux aux.
    by rewrite eval_dual_f.

    (* Caso: Conj *)
    rewrite /Teorema => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    rewrite dual_conj eval_conj eval_conj.
    by rewrite eval_dual_f eval_dual_f.

    (* Caso: Or *)
    rewrite /Teorema => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    rewrite dual_or eval_or eval_or.
    by rewrite eval_dual_f eval_dual_f.

    (* Caso: Imp *)
    rewrite /Teorema => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_lattice_of L) z env).
    rewrite dual_imp eval_imp eval_imp.
    by rewrite eval_dual_f eval_dual_f.
Qed.
(*    Fin del Teorema de dualidad     *)

Lemma Dual : forall f : Form, (Teorema f) <-> (Teorema (dual f)).
Proof.
move=> f.
split.
  by move: (Dualidad f).
move: (Dualidad (dual f))=> H.
by rewrite {2}(duald f).
Qed.