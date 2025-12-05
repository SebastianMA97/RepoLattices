From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


Lemma dobl (A : Prop) :  A <-> A /\ A.
Proof.
split. by [].
move=> [h1 h2]; by [].
Qed.


Section Lattices.
Definition reflexive {T : Type} (rel : T -> T -> Prop) : Prop := forall x :T, rel x x.
Definition antisymetric {T : Type} (rel : T -> T -> Prop) : Prop := forall x y : T, (rel x y) -> (rel y x) -> (x = y).
Definition transitive {T : Type} (rel : T -> T -> Prop) :Prop := forall x y z :T, rel x y -> rel y z -> rel x z.
Definition order {T : Type} (rel : T -> T -> Prop) := reflexive rel /\ antisymetric rel /\ transitive rel.

Structure ordenParcial := OrdenParcial
  {
    O :> Type;
    ord : O -> O -> Prop;
    reflexT : reflexive ord;
    antisymT : antisymetric ord;
    transT : transitive ord;
  }.
Notation "x ≤ y" := (ord _ x y) (at level 50).

Structure lattice := Lattice 
  { 
    T :> ordenParcial;
    joinT : T -> T -> T;
    jHT : (forall z : T , forall x y : T,  (x ≤ z /\ y ≤ z) <->( joinT x y) ≤ z);
    meetT : T -> T -> T;
    mHT : (forall z : T , forall x y : T,  (z ≤ x /\ z ≤ y) <-> z ≤ ( meetT x y))
   }.
Notation "x ⊓ y" := (@meetT _ x y) (at level 50). (* \sqcap *)
Notation "x ⊔ y" := (@joinT _ x y) (at level 50). (* \sqcup *)
Notation reflex := (reflexT _).
Notation antisym := (antisymT _).
Notation trans := (transT _).
Notation JH := (@jHT _).
Notation MH := (@mHT _).

(* Para el teorema de dualidad *)

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

Fixpoint eval (L : lattice) (env : nat -> L) (t : Term) : L :=
  match t with
  | Var n     => env n
  | Meet t1 t2 => @meetT L (eval L env t1) (eval L env t2)
  | Join t1 t2 => @joinT L (eval L env t1) (eval L env t2)
  end.

Inductive Form : Set :=
| f_leq  : Term -> Term -> Form
| f_eq   : Term -> Term -> Form
| f_neg  : Form -> Form
| f_conj : Form -> Form -> Form
| f_or   : Form -> Form -> Form
| f_imp  : Form -> Form -> Form.

Fixpoint eval_f (L : lattice) (env : nat -> L) (f : Form) : Prop :=
  match f with
  | f_leq t1 t2 => (eval L env t1) ≤ (eval L env t2)
  | f_eq t1 t2  => (eval L env t1) = (eval L env t2)
  | f_neg f1     => ~ (eval_f L env f1)
  | f_conj f1 f2  => eval_f L env f1 /\ eval_f L env f2
  | f_or f1 f2    => (eval_f L env f1) \/ (eval_f L env f2)
  | f_imp f1 f2   =>  (eval_f L env f1) -> (eval_f L env f2)
  end.

Definition Teorema (F : Form) : Prop :=
forall (L : lattice) (env : nat -> L), (eval_f L env F).

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

Lemma  eval_m : forall (L : lattice) (env : nat -> L) (t0 t1 : Term), 
              eval L env (Meet t0 t1) = meetT L (eval L env t0) (eval L env t1).
Proof. by move=> L0 env0; rewrite /eval. Qed.

Lemma eval_j : forall (L : lattice) (env : nat -> L) (t0 t1 : Term), 
              eval L env (Join t0 t1) = joinT L (eval L env t0) (eval L env t1).
Proof. by move=> L0 env0; rewrite /eval. Qed.

Lemma eval_conj : forall (L : lattice) (env : nat -> L) (f0 f1 : Form), 
                   eval_f L env (f_conj f0 f1) = and (eval_f L env f0) (eval_f L env f1).
Proof.  by []. Qed.

Lemma dual_conj : forall (f0 f1 : Form), dual (f_conj f0 f1) = f_conj (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma eval_or : forall (L : lattice) (env : nat -> L) (f0 f1 : Form), 
                   eval_f L env (f_or f0 f1) = or (eval_f L env f0) (eval_f L env f1).
Proof.  by []. Qed.

Lemma dual_or : forall (f0 f1 : Form), dual (f_or f0 f1) = f_or (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma eval_imp : forall (L : lattice) (env : nat -> L) (f0 f1 : Form), 
                   eval_f L env (f_imp f0 f1) =(( eval_f L env f0) -> (eval_f L env f1)).
Proof. by []. Qed.

Lemma dual_imp : forall (f0 f1 : Form), dual (f_imp f0 f1) = f_imp (dual f0) (dual f1).
Proof.  by []. Qed.

Lemma dual_m : forall t0 t1 : Term, 
                dual_t (Meet t0 t1) = Join (dual_t t0) (dual_t t1).
Proof.  by move=> t2 t3; rewrite /dual_t. Qed.

Lemma dual_j : forall t0 t1 : Term, 
                dual_t (Join t0 t1) = Meet (dual_t t0) (dual_t t1).
Proof.  by move=> t2 t3; rewrite /dual_t. Qed.

Theorem eval_dual (L : lattice) (env : nat -> L) (t : Term) :
  eval (dual_lattice_of L) env t = eval L env (dual_t t).
Proof.
elim t.
  (* Var n *)
  move=> n0.
  by rewrite {1}/eval/dual_t/eval.
  
  (* Meet t0 t1*)
  move=> t0 H0 t1 H1.
  rewrite dual_m (eval_j L env).
  rewrite (eval_m (dual_lattice_of L) env).
  by rewrite H0 H1 mldj.

  (* Join t0 t1 *)
  move=> t0 H0 t1 H1.
  rewrite dual_j (eval_m L env).
  rewrite (eval_j (dual_lattice_of L) env).
  by rewrite H0 H1 jldm.
Qed.

Lemma le_dual (L : lattice) (x y : L) :
  (ord (dual_lattice_of L) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Theorem eval_dual_f (L : lattice) (env : nat -> L) (f : Form) :
  eval_f (dual_lattice_of L) env f = eval_f L env (dual f).
Proof.
elim f.
  (* Term *)
  move=> t0 t1.
  by rewrite /dual /eval_f eval_dual eval_dual.
  
  move=> t0 t1.
  by rewrite /dual /eval_f eval_dual eval_dual.
  
  (* Neg *)
  move=> f0 H0.
  have aux: forall (L : lattice) (env : nat -> L) (f0 : Form), eval_f L env (f_neg f0) = ~ (eval_f L env f0).
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


Theorem Dualidad : forall f : Form, (Teorema f) -> (Teorema (dual f)).
Proof.
move=> f.
elim f.
  move=> t0 t1.

    (* Caso: leq *)

    rewrite /dual /Teorema => Hip L env.
    move: (Hip (dual_lattice_of L) env).
    by rewrite eval_dual_f /dual.

    (* Caso: eq *)
    
    rewrite /Teorema /dual /eval_f => t0 t1 Hip L env.
    move: (Hip (dual_lattice_of L) env).
    by rewrite eval_dual eval_dual.

    (* Caso: neg *)
    rewrite /Teorema => f0 _ Hip L env.
    move: (Hip (dual_lattice_of L) env).
    have aux: forall (L : lattice) (env : nat -> L) (f0 : Form), eval_f L env (f_neg f0) = ~ (eval_f L env f0).
      by [].
    have auxd: forall (f0 : Form), dual (f_neg f0) = f_neg (dual f0).
      by [].
    rewrite auxd aux aux.
    by rewrite eval_dual_f.

    (* Caso: Conj *)
    rewrite /Teorema => f0 _ f1 _ Hip L env.
    move: (Hip (dual_lattice_of L) env).
    rewrite dual_conj eval_conj eval_conj.
    by rewrite eval_dual_f eval_dual_f.

    (* Caso: Or *)
    rewrite /Teorema => f0 _ f1 _ Hip L env.
    move: (Hip (dual_lattice_of L) env).
    rewrite dual_or eval_or eval_or.
    by rewrite eval_dual_f eval_dual_f.

    (* Caso: Imp *)
    rewrite /Teorema => f0 _ f1 _ Hip L env.
    move: (Hip (dual_lattice_of L) env).
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

(* Ahorrarme tiempo Prop -> Form *)
Inductive Elem : Set :=
| V  : nat -> Elem
| M : Elem -> Elem -> Elem
| J : Elem -> Elem -> Elem.
Notation "x e⊓ y" := (M x y) (at level 50). (* \sqcap *)
Notation "x e⊔ y" := (J x y) (at level 50). (* \sqcup *)

Inductive Felem : Set :=
| eleq  : Elem -> Elem -> Felem
| eeq   : Elem -> Elem -> Felem
| eneg  : Felem -> Felem
| econj : Felem -> Felem -> Felem
| eor   : Felem -> Felem -> Felem
| eimp  : Felem -> Felem -> Felem.

Notation "x e≤ y" := (eleq x y) (at level 50).
Notation "x e= y" := (eeq x y) (at level 50).
Notation "e~ f" := (eneg f) (at level 50).
Notation "x e/\ y" := (econj x y) (at level 50).
Notation "x e\/ y" := (eor x y) (at level 50).
Notation "x e-> y" := (eimp x y) (at level 50).

Fixpoint transE (e : Elem) : Term :=
  match e with
  | V n     => Var n
  | M e1 e2 => Meet (transE e1) (transE e2)
  | J e1 e2 => Join (transE e1) (transE e2)
  end.

Fixpoint transF (f : Felem) : Form :=
 match f with
  | eleq e1 e2 => f_leq (transE e1) (transE e2)
  | eeq e1 e2  => f_eq (transE e1) (transE e2)
  | eneg f1    => f_neg (transF f1)
  | econj f1 f2 => f_conj (transF f1) (transF f2)
  | eor f1 f2  => f_or (transF f1) (transF f2)
  | eimp f1 f2 => f_imp (transF f1) (transF f2)
 end.


       (*  Así se harán las pruebas con dualidad  *)
Lemma intento {T : lattice} : forall a b : T , a ≤ (a ⊔ b).
Proof.
move=> a b.
by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj1.
Qed.

Definition env_ab {L : lattice} (a b : L) (n : nat) : L :=
  if n == 0 then a else b.


Lemma intentoDual {L : lattice} : forall a b : L , (a ⊓ b) ≤ a.
Proof.
move=> a b.

(* Subimos intento a -> un Teorema (Form) *)
have teo : Teorema (transF(V 0 e≤ (V 0 e⊔ V 1))).
  simpl.
  rewrite /Teorema/eval_f/eval => L0 env.
  by move: ((@intento L0) (env 0) (env 1)).
(* Esto es forzosamente dentro de la prueba *)

(* Ahora hacemos <> Teorema de dual(Form) *)
move: teo; rewrite Dual/dual/dual_t/Teorema.

(* Bajamos evaluando a nuestra lattice <- Teorema de dual(Form) *)
move=> /(_ L (@env_ab L a b)).
by rewrite /eval_f/eval/env_ab.
(* pensar una función env que asigne a1 a2 a3 ... ai a los primeros i nat *)
Qed.


Lemma ab_leq_jab {T : lattice} : forall a b : T ,   a ≤ (a ⊔ b) /\  b ≤ (a ⊔ b).
Proof.
move=> a b.
split.
  by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj1.
by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj2.
Qed.

Lemma mab_leq_ab {T : lattice} : forall a b : T ,  (a ⊓ b) ≤ a /\ (a ⊓ b) ≤ b.
Proof.
move=> a b.

(* Subimos intento a -> un Teorema (Form) *)
have teo : Teorema (transF(V 0 e≤ (V 0 e⊔ V 1) e/\ (V 1 e≤ (V 0 e⊔ V 1)))).
  rewrite /Teorema/eval_f/eval => L0 env.
  by move: ((ab_leq_jab) (env 0) (env 1)).

(* Ahora hacemos <> Teorema de dual(Form) *)
move: teo; rewrite Dual/dual/dual_t.

(* Bajamos evaluando a nuestra lattice <- Teorema de dual(Form) *)
rewrite /Teorema => /(_ T (@env_ab T a b)).
by rewrite /eval_f/eval/env_ab.
Qed.

Lemma ConnectJ {T : lattice} : forall a b : T ,  a ≤ b <-> (a ⊔ b = b).
Proof.
split.
move=> abLeq.
  apply: antisym.
    rewrite -(JH).
    split.
      by [].
    by apply: reflex.
  move: (reflex (a ⊔ b)).
  by rewrite -(JH) => /proj2.
move=> H.
move: (reflex (a ⊔ b)).
rewrite {2}H.
move: (ab_leq_jab a b) => /proj1.
by apply: trans.
Qed.

Lemma ConnectM {T : lattice} : forall a b : T , a ≤ b <-> (b ⊓ a = a).
Proof.
move=> a b; rewrite /iff.
have teo : Teorema (transF(( V 0 e≤ V 1 e-> (V 0 e⊔ V 1 e= V 1))
                                       e/\ ((V 0 e⊔ V 1 e= V 1) e-> (V 0 e≤ V 1) ))).
  rewrite /Teorema/eval_f/eval => L0 env.
  by move: ((ConnectJ) (env 0) (env 1)); rewrite /iff.
move: teo; rewrite Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_ab T b a)).
by rewrite /eval_f/eval/env_ab.
Qed.

(* Propiedades L1 a L4*)

Lemma L3 {T : lattice} : forall a : T , a ⊔ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /ConnectJ.
Qed.

Lemma L3d {T : lattice} : forall a : T , a ⊓ a = a.
Proof.
move=> a.
have teo : Teorema (transF(V 0 e⊔ V 0 e= V 0)).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (L3 (env 0)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (fun n => a)).
by rewrite /eval_f/eval.
Qed.

Lemma L2 {T : lattice} : forall a b : T , a ⊔ b = b ⊔ a.
Proof.
move=> a b.
apply: antisym.
  move: (ab_leq_jab b a) => /and_comm.
  by rewrite JH. 
move: (ab_leq_jab a b) => /and_comm.
by rewrite JH.
Qed.

Lemma L2d {T : lattice} : forall a b : T , a ⊓ b = b ⊓ a.
Proof.
move=> a b.
(*Por Dualidad de L2*)
have teo : Teorema (transF(V 0 e⊔ V 1 e= (V 1 e⊔ V 0))).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (L2 (env 0) (env 1)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_ab T b a)).
by rewrite /eval_f/eval/env_ab.
Qed.

Lemma L4 {T : lattice} : forall a b : T , a ⊔ (a ⊓ b) = a.
Proof.
move=> a b.
move: (mab_leq_ab a b) => /proj1.
move=> /ConnectJ.
by rewrite L2.
Qed.

Lemma L4d {T : lattice} : forall a b : T , a ⊓ (a ⊔ b) = a.
Proof.
move=> a b.
(*Por Dualidad*)
have teo : Teorema (transF(V 0 e⊔ (V 0 e⊓ V 1) e= V 0)).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (L4 (env 0) (env 1)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_ab T a b)).
by rewrite /eval_f/eval/env_ab.
Qed.

Definition env_abc {L : lattice} (a b c : L) (n : nat) :=
  if n == 0 then a else (if n == 1 then b else c).

Lemma L1 {T : lattice} : forall a b c : T , (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof. 
have c_leq_jab: forall x y z : T , z ≤ y -> z ≤ (x ⊔ y).
    move=> x y z z_leq_y; move: (ab_leq_jab x y) => /proj2.
    move: z_leq_y; by apply: trans.
move=> a b c.
apply: antisym.
  rewrite -JH.
  split.
    rewrite -JH.
    split.
      by move: (ab_leq_jab a (b ⊔ c)) => /proj1. (*1° caso a ≤ sup a (sup b c)*)
    by move: (ab_leq_jab b c) => /proj1 /c_leq_jab. (*2° caso b ≤ sup a (sup b c)*)
  by move: (ab_leq_jab b c) => /proj2 /c_leq_jab. (*c ≤ sup a (sup b c)*)
rewrite -JH.
split.
  rewrite L2.
  move: (ab_leq_jab a b) => /proj1.
  by move=> /c_leq_jab.
rewrite -JH.
split.
  move: (ab_leq_jab a b) => /proj2; rewrite [_ ⊔ c](L2).
  by move=> /c_leq_jab.  (*sup c (sup a b)*)
by move: (ab_leq_jab (a ⊔ b) c) => /proj2. (*c ≤ sup (sup a b) c*)
Qed.

Lemma L1d {T : lattice} : forall a b c : T , (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. 
move=> a b c.
(*Por Dualidad*)
have teo : Teorema (transF((V 0 e⊔ V 1) e⊔ V 2 e= (V 0 e⊔ (V 1 e⊔ V 2)))).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (L1 (env 0) (env 1) (env 2)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_abc T a b c)).
by rewrite /eval_f/eval/env_abc.
Qed.

Structure latticeAlg := LatticeAlg 
  {
    A :> Type;
    j : A -> A -> A;
    m : A -> A -> A;
    l1 : forall a b c : A, j (j a b) c = j a (j b c);
    l1d : forall a b c : A, m (m a b) c = m a (m b c);
    l2 : forall a b : A, j a b = j b a;
    l2d : forall a b : A, m a b = m b a;
    l3 : forall a : A, j a a = a;
    l3d : forall a : A, m a a = a;
    l4 : forall a b : A, j a (m a b) = a;
    l4d : forall a b : A, m a (j a b) = a
  }.
Notation "x ∧ y" := (@m _ x y) (at level 50). (* \wedge *)
Notation "x ∨ y" := (@j _ x y) (at level 50). (* \vee *)
Notation L1_Alg := (l1 _).
Notation L1d_Alg := (l1d _).
Notation L2_Alg := (l2 _).
Notation L2d_Alg := (l2d _).
Notation L3_Alg := (l3 _).
Notation L3d_Alg := (l3d _).
Notation L4_Alg := (l4 _).
Notation L4d_Alg := (l4d _).

Check @joinT.

Canonical Alg_lattice {T : lattice} := LatticeAlg T (@joinT T) (@meetT T) L1 L1d L2 L2d L3 L3d L4 L4d.

Lemma AlgToSet1 {T : latticeAlg} : forall a b : T, ( a ∨ b = b) <-> ( a ∧ b = a).
Proof.
split.
  move=> jab_b.
  move: (L4d_Alg a b).
  by rewrite jab_b.
move=> mab_a.
move: (L4_Alg b a).
by rewrite L2d_Alg mab_a L2_Alg.
Qed.

Definition nord {T : latticeAlg} (a b : T) := (a ∨ b = b).
Notation "x ≼ y" := (@nord _ x y) (at level 50). (* \preccurlyeq *)

Lemma AlgToSetReflex {T : latticeAlg} : reflexive (@nord T).
Proof.
  move=> a.
  rewrite /nord.
  by apply: L3_Alg.
Qed.

Lemma AlgToSetAntisym {T : latticeAlg} : antisymetric (@nord T).
Proof.
  move=> a b.
  rewrite /nord => supb.
  by rewrite L2_Alg supb.
Qed.

Lemma AlgToSetTrans {T : latticeAlg} : transitive (@nord T).
Proof.
move=> a b c.
rewrite /nord.
move=> supab supbc.
by move: (L1_Alg a b c); rewrite supab supbc.
Qed.

Canonical T_ordenParcial {T : latticeAlg} := OrdenParcial T (@nord T) AlgToSetReflex AlgToSetAntisym AlgToSetTrans.


Lemma AlgToSet_joinAlg {T : latticeAlg} : forall z : T, (forall x y : T, (x ≼ z /\ y ≼ z) <-> (x ∨ y) ≼ z).
Proof.
move=> z x y.
split.
  rewrite /nord.
  move=> [supxz supyz].
  by move: supxz; rewrite -{1}(supyz) -L1_Alg.
move=> H1.
have cotaS: forall a b : T, (a ≼ (a ∨ b)) /\ (b ≼ (a ∨ b)).
  move=> a b.
  split.
    by rewrite /nord -L1_Alg L3_Alg.
  by rewrite /nord L2_Alg L1_Alg L3_Alg.
split.
  move: (cotaS x y) H1 => /proj1.
  by apply: AlgToSetTrans.
move: H1; move: (cotaS x y); move=> /proj2.
by apply: AlgToSetTrans.
Qed.

Lemma AlgToSet_meetAlg {T : latticeAlg}: forall z : T, (forall x y : T, (z ≼ x /\ z ≼ y) <-> z ≼ (x ∧ y) ).
Proof.
move=> z x y.
split.
  rewrite /nord.
  move => [/(AlgToSet1)-H1 /(AlgToSet1)-H2].
  rewrite AlgToSet1.
  move: H1.
  by rewrite -{1}(H2) L1d_Alg (L2d_Alg y x).
move=> H1.
have cotaI: forall a b : T, ((a ∧ b) ≼ a) /\ ((a ∧ b) ≼ b).
  move=> a b.
  split.
    by rewrite /nord AlgToSet1 (L2d_Alg) -(L1d_Alg) L3d_Alg.
  by rewrite /nord AlgToSet1 L1d_Alg L3d_Alg.
split.
  move: (cotaI x y) => /proj1; move: H1. 
  by apply: AlgToSetTrans.
move: (cotaI x y) => /proj2; move: H1.
by apply: AlgToSetTrans.
Qed.

Canonical T_lattice {T : latticeAlg} := Lattice (OrdenParcial T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans)
                       (@j _) AlgToSet_joinAlg (@m _) AlgToSet_meetAlg.

Lemma join_eq {T : latticeAlg}: forall a b : T,  a ∨ b = joinT T_lattice a b.
Proof. by []. Qed.

Lemma meet_eq {T : latticeAlg}: forall a b : T, a ∧ b = meetT T_lattice a b.
Proof. by []. Qed.

(* Proposición 2.19 *)

Definition ordPreserv {L K : lattice} {f : L -> K} 
                      := forall a b : L, a ≤ b -> (f a) ≤ (f b).

Definition ordEmmbed {L K : lattice} {f : L -> K}
                     := forall a b : L, a ≤ b <-> (f a) ≤ (f b).

Definition Biyective {L K : lattice} {f : L -> K}
                     := (forall a b : L, (f a) = (f b) <-> a = b) /\ (forall b : K, (exists a : L, b = f a )).

Definition ordIso {L K : lattice} {f : L -> K} := (@Biyective L K f) /\ (@ordEmmbed L K f) .

Definition joinOrdPreserv {L K : lattice} {f : L -> K}
                          := forall x y : L, (f x) ⊔ (f y) ≤ f (x ⊔ y) .

Definition meetOrdPreserv {L K : lattice} {f : L -> K}
                          := forall x y : L, f (x ⊓ y) ≤ ((f x) ⊓ (f y)).

Definition joinPreserv {L K : lattice} {f : L -> K}
                       := forall x y : L, (f x) ⊔ (f y) = f (x ⊔ y).

Definition meetPreserv {L K : lattice} {f : L -> K}
                       := forall x y : L, f (x ⊓ y) = (f x) ⊓ (f y).

Definition latticeIso {L K : lattice} {f : L -> K}
                      := (@joinPreserv L K f) /\ (@meetPreserv L K f) /\ (@Biyective L K f).

Lemma prop219i1 {L K : lattice} {f : L -> K} : (@ordPreserv L K f)  <-> (@joinOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (ab_leq_jab a b) => [/(ordenP)-cota_fa /(ordenP)-cota_fb].
  rewrite -JH.
  by split.
rewrite /joinOrdPreserv => H.
move=> a b /ConnectJ-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab (f a) (f b)) => /proj1.
by apply: trans.
Qed.


Lemma prop219i2 {L K : lattice} {f : L -> K} : (@ordPreserv L K f) <-> (@meetOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (mab_leq_ab a b) => [/ordenP-cota_fa /ordenP-cota_fb].
  move: (conj cota_fa cota_fb).
  by rewrite MH.
rewrite /meetOrdPreserv => H.
move=> a b /ConnectM; rewrite L2d => mab_L.
move: (mab_leq_ab (f a) (f b)) => /proj2.
move: (H a b); rewrite mab_L.
by apply: trans.
Qed.

Lemma prop219i3 {L K : lattice} {f : L -> K} : (@ordIso L K f) <-> (@latticeIso L K f).
Proof.
split.
  rewrite /ordIso /ordEmmbed /Biyective; move=> [[inj sob] H].
  rewrite /latticeIso. 
  split.
    move=> x y; apply: antisym.
      move: (@prop219i1 L K f); rewrite /ordPreserv /joinOrdPreserv => /proj1-H2.
      apply: H2 => c d.
      by move: (H c d) => /proj1.
    move: (sob ((f x) ⊔ (f y))) => [a Ha].
    move: (ab_leq_jab (f x) (f y)).
    rewrite Ha; move=> [/H-xleqa /H-yleqa].
    by rewrite -H -JH.
  split.
    move=> x y; apply: antisym.
      move: (@prop219i2 L K f); rewrite /ordPreserv /meetOrdPreserv => /proj1-H2.
      apply: H2 => c d;
      by move: (H c d) => /proj1.
      move: (sob ((f x) ⊓ (f y))) => [a Ha].
      move: (mab_leq_ab (f x) (f y)).
      rewrite Ha; move=> [/H-aleqx /H-aleqy].
      by rewrite -H -MH.
    by [].
rewrite /latticeIso; move=> [Hjoin [Hmeet [inj sob]]].
split.
  by [].
move=> a b.
split.
  by move=> /ConnectJ /inj; rewrite -Hjoin -ConnectJ.
by rewrite ConnectJ Hjoin inj -(ConnectJ).
Qed.

(* Lattices modulares, distributivas y booleanas *)

Lemma Lema4_1i {T : lattice} : forall a b c : T, ((a ⊓ b) ⊔ (a ⊓ c)) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c.
rewrite -MH.
split.
  rewrite -JH.
  split.
    by move: (mab_leq_ab a b) => /proj1.
  by move: (mab_leq_ab a c) => /proj1.
rewrite -JH.
move: (ab_leq_jab b c) => [cota_b cota_c].
split.
  move: (mab_leq_ab a b) cota_b => /proj2.
  by apply: trans.
move: (mab_leq_ab a c) cota_c => /proj2.
by apply: trans.
Qed.

Lemma Lema4_1id {T : lattice} : forall a b c : T, (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ (a ⊔ c)).
Proof.
move=> a b c.
(*Por Dualidad*)
have teo : Teorema (transF(((V 0 e⊓ V 1) e⊔ (V 0 e⊓ V 2)) e≤ (V 0 e⊓ (V 1 e⊔ V 2)))).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (Lema4_1i (env 0) (env 1) (env 2)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_abc T a b c)).
by rewrite /eval_f/eval/env_abc.
Qed.

Lemma Lema4_1ii {T : lattice} : forall a b c : T, c ≤ a -> ((a ⊓ b) ⊔ c) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c /ConnectM- H.
by move: (Lema4_1i a b c); rewrite H.
Qed.

Lemma Lema4_1iid {T : lattice} : forall a b c : T, a ≤ c -> (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ c).
Proof.
move=> a b c.
(*Por Dualidad*)
have teo : Teorema (transF(V 2 e≤ V 0 e-> ( ((V 0 e⊓ V 1) e⊔ V 2) e≤ (V 0 e⊓ (V 1 e⊔ V 2)) ) )).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (Lema4_1ii (env 0) (env 1) (env 2)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_abc T a b c)).
by rewrite /eval_f/eval/env_abc.
Qed.

Lemma Lema4_1iii {T : lattice} : forall a b c : T, ((a ⊓ b) ⊔ (b ⊓ c) ⊔ (c ⊓ a)) ≤ ((a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a)).
Proof.
have aux : forall a b c : T, (a ⊓ b) ≤ (c ⊔ a).
  move=> a b c; move: (ab_leq_jab c a)=> /proj2.
  move: (mab_leq_ab a b) => /proj1.
  by apply: trans.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    have H1 : b ≤ ((a ⊔ b) ⊓ (b ⊔ c)).
      rewrite -MH.
      split.
        by move: (ab_leq_jab a b) => /proj2.
      by move: (ab_leq_jab b c) => /proj1.
    have H2 : ((a ⊓ b) ⊔ (b ⊓ c)) ≤ b.
      rewrite -JH.
      split.
        by move: (mab_leq_ab a b) => /proj2.
      by move: (mab_leq_ab b c) => /proj1.
    by move: H1; move: H2; apply: trans.
  rewrite -JH.
  split.
    by apply: aux.
  by rewrite (L2d) (L2); apply aux.
rewrite -MH.
split.
  rewrite -MH.
  split.
    by rewrite (L2d) (L2); apply aux.
  by apply: aux.
by rewrite L2; apply: aux.
Qed.


Lemma Lema4_2i {T : lattice} : forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)) <->
                                   (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))).
Proof.
split. 
  by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite H.
by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite H.
Qed.

Lemma Lema4_2ii {T : lattice} : (forall a b c : T, c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))) <->
                  (forall p q r : T, (p ⊓ (q ⊔ (p ⊓ r))) = ((p ⊓ q) ⊔ (p ⊓ r))).
Proof.
split.
  move=> H p q r.
  move: (mab_leq_ab p r) => /proj1.
  rewrite (Lema4_2i).
  by apply: H.
move=> H a b c /ConnectM-cleqa.
rewrite -{1}cleqa. 
by apply: H.
Qed.

Lemma Lema4_3 {T : lattice} : (forall a b c : T, (a ⊓ (b ⊔ c)) = (a ⊓ b) ⊔ (a ⊓ c)) <-> 
                (forall p q r : T, (p ⊔ (q ⊓ r)) = (p ⊔ q) ⊓ (p ⊔ r)).
Proof.
split.
  move=> H p q r.
  move: (H (p ⊔ q) p r).
  rewrite [(p ⊔ q) ⊓ p]L2d [p ⊓ (p ⊔ q)]L4d [(p ⊔ q) ⊓ r]L2d.
  rewrite (H r p q).
  by rewrite -L1 [r ⊓ p]L2d [p ⊔ (p ⊓ r)]L4 [r ⊓ q]L2d.
move=> H a b c.
move: (H (a ⊓ b) a c).
rewrite [(a ⊓ b) ⊔ a]L2 [a ⊔ (a ⊓ b)]L4.
rewrite [(a ⊓ b) ⊔ c]L2 (H c a b).
by rewrite -L1d [c ⊔ a]L2 [a ⊓ (a ⊔ c)]L4d [c ⊔ b]L2.
Qed.

Definition Distributive {T : lattice} := forall a b c : T, (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c)).

Definition Modular := forall (T : lattice) (a b c : T), (c ≤ a -> (c ⊔ (b ⊓ a)) = ((c ⊔ b) ⊓ a)). 

Definition Modu_L (L : lattice) := forall a b c : L, (c ≤ a -> (c ⊔ (b ⊓ a)) = ((c ⊔ b) ⊓ a)).

Lemma Modular2 {T : lattice} (P : Modu_L T) : forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)).
Proof.
move: P; rewrite /Modu_L.
move=> H a b c.
move=> /(H a b c).
by rewrite L2 [b ⊓_]L2d [_ ⊓ a]L2d [c ⊔ _]L2.
Qed.
 
Lemma ModularD {T : lattice} (Mod : Modular) : forall a b c : T, (a ≤ c -> (a ⊔ (b ⊓ c)) = ((a ⊔ b) ⊓ c)).
Proof.
move=> a b c.
(*Por Dualidad*)
have teo : Teorema (transF( (V 2 e≤ V 0) e-> ((V 0 e⊓ (V 1 e⊔ V 2)) e= ((V 0 e⊓ V 1) e⊔ V 2)) )).
  rewrite /transF/transE /Teorema/eval_f/eval => L0 env.
  by move: (Modular2 (Mod L0) (env 0) (env 1) (env 2)).
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_abc T a b c)).
by rewrite /eval_f/eval/env_abc.
Qed.

Lemma ModularD2 {T : lattice} : (forall a b c : T, (a ≤ c -> (a ⊔ (b ⊓ c)) = ((a ⊔ b) ⊓ c)))
                -> (forall a b c : T, (a ≤ c -> ( c ⊓ (b ⊔ a)  = (c ⊓ b) ⊔ a ))).
Proof.
move=> H a b c.
move=> /(H _ b).
by rewrite L2 [b ⊓ c]L2d [_ ⊓ c]L2d [a ⊔ b]L2.
Qed.


Structure boundedLattice := BoundedLattice 
  {
    BL :> lattice;
    Top : BL;
    Bot : BL;
    Top_Bottom : forall a : BL, a ≤ Top /\ Bot ≤ a
  }.
Notation  top := (Top _).
Notation  bot := (Bot _).
Notation TB := (Top_Bottom _).

Structure booleanLattice := BooleanLattice
  {
    BooL :> boundedLattice;
    Distr: (@Distributive BooL);
    ExComplement : forall a : BooL, (exists b, (a ⊔ b = top ) /\ (a ⊓ b = bot) ) 
  }.
Notation Dist := (Distr _).
Notation ExComp := (ExComplement _).

Lemma ajBot {T : boundedLattice} : forall a : T, a ⊔ bot = a.
Proof.
move=> a.
rewrite L2 -ConnectJ.
by move: (TB a) => /proj2.
Qed.

Lemma amTop {T : boundedLattice} : forall a : T, a ⊓ top = a.
Proof.
move=> a.
rewrite L2d -ConnectM.
by move: (TB a) => /proj1.
Qed.

Definition Comp {T : boundedLattice} (a b : T ):= (a ⊔ b = top) /\ (a ⊓ b = bot).
 
Lemma compUnico {T : booleanLattice} : forall a b c : T,
                (Comp a b /\ 
                Comp a c) -> b = c.
Proof.
move=> a b c.
rewrite /Comp. 
move=> [[H0 H1] [H2 H3]].
apply: antisym.
  rewrite ConnectM.
  rewrite -{2}(amTop b).
  rewrite -H2.
  rewrite Dist.
  by rewrite [b ⊓ a]L2d H1 L2 ajBot L2d.
rewrite ConnectM.
rewrite -{2}(amTop (c)).
rewrite -H0.
rewrite Dist.
by rewrite  [c ⊓ a]L2d H3 L2 ajBot L2.
Qed.

Lemma lema4_15i {T : booleanLattice} : (@Comp T top bot).
Proof.
split.
  move: (@Top_Bottom T top) => /proj2.
  by rewrite ConnectJ L2.
move: (@Top_Bottom T bot) => /proj1.
by rewrite ConnectM L2d.
Qed.

Lemma lema4_15ii {T : booleanLattice} : forall a b c : T, Comp a b -> Comp b c -> c = a.
Proof.
move=> a b c.
rewrite /Comp.
rewrite L2 L2d.
move=> [H0 H1] [H2 H3].
apply: (compUnico b).
rewrite /Comp.
by split.
Qed.
 
Lemma lema4_15iii {T : booleanLattice} : forall a b caub ca cb canb : T, 
                                         (Comp (a ⊔ b) caub -> Comp a ca -> Comp b cb -> (caub = ca ⊓ cb))
                                         /\ (Comp (a ⊓ b) canb -> Comp a ca -> Comp b cb -> (canb = ca ⊔ cb)).
Proof.
move=> a b caub ca cb canb.
move: (Distr T).
rewrite /Distributive Lema4_3 => Dis.
split.
  rewrite /Comp.
  move=> [H0 H1] [H2 H3] [H4 H5].
  apply: (compUnico (a ⊔ b)).
  split.
    by [].
  split.
    rewrite Dis {1}[a ⊔ b]L2 L1 H2.
    rewrite L1 H4.
    move: (TB b) (TB a).
    move=> /proj1/ConnectJ-bTop /proj1/ConnectJ-aTop.
    by rewrite bTop aTop amTop.
  rewrite L2d Dist L2d -L1d H3.
  rewrite L1d [cb ⊓ b]L2d H5.
  move: (TB cb) (TB ca).
  move=> /proj2/ConnectM-eBot /proj2/ConnectM-dBot.
  by rewrite L2d eBot dBot ajBot.
rewrite /Comp.
move=> [H0 H1] [H2 H3] [H4 H5].
apply: (compUnico (a ⊓ b)).
split.
  by [].
split.
  rewrite L2 Dis L2 -L1 H2 L2.
  rewrite L1 [cb ⊔ b]L2 H4.
  move: (TB cb) (TB ca).
  move=> /proj1/ConnectJ-eTop /proj1/ConnectJ-dTop.
  by rewrite eTop dTop amTop.
rewrite Dist [a ⊓ b]L2d L1d H3 L2d.
rewrite [b ⊓ a]L2d L1d H5 [a ⊓ bot]L2d.
move: (TB b) (TB a).
move=> /proj2/ConnectM-bBot /proj2/ConnectM-aBot.
by rewrite L2d bBot L2d aBot ajBot.
Qed.
 
Lemma lema4_15v {T : booleanLattice} : forall a b c : T, Comp b c -> a ⊓ c = bot <-> a ≤ b.
Proof.
move=> a b c.
move: (Distr T).
rewrite /Distributive Lema4_3 => DistD.
move=> /dobl [CB [H0 H1]].
split.
  move=> H2.
  rewrite ConnectM.
  move: (amTop a).
  by rewrite -H0 Dist H2 ajBot L2d.
rewrite ConnectJ => H.
move: (ExComp a).
case => a0 [aTop aBot].
have CA : Comp a a0.
  by [].
move: (TB c) => /proj2.
rewrite ConnectM -{1}aBot L2d L1d.
move: (lema4_15iii a b c a0 c (a ⊓ b) ) => /proj1.
rewrite H.
move=> /(_ CB) /(_ CA) /(_ CB)-Compl.
by rewrite -Compl.
Qed.


(* Aquí empiezo a implementar del libro de Curry por el momento *)
 
Theorem RpJ {T : lattice}: forall a b c : T, a ≤ b -> c ⊔ a ≤ (c ⊔ b).
Proof.
move=> a b c H.
rewrite -JH.
split.
  by move: (ab_leq_jab c b) => /proj1.
move: (ab_leq_jab c b) => /proj2.
move: H.
by apply: trans.
Qed.

Theorem RpM {T : lattice}: forall a b c : T, a ≤ b -> c ⊓ a ≤ (c ⊓ b).
Proof.
move=> a b c H.
rewrite -MH.
split.
  by move: (mab_leq_ab c a) => /proj1.
move: H.
move: (mab_leq_ab c a) => /proj2.
by apply: trans.
Qed.

Lemma siml {T : lattice} :  forall a b : T, a = b -> a ≤ b.
Proof.
move=> x y Hip.
rewrite Hip.
move: (reflex y)=>H.
by [].
Qed.

Lemma simr {T : lattice} :  forall a b : T, a = b -> b ≤ a.
Proof.
move=> x y Hip.
rewrite Hip.
move: (reflex y)=>H.
by [].
Qed.


Lemma mW {T : lattice} : forall a : T, a ≤ (a ⊓ a).
Proof.
move=> a.
move: (reflex a)=> H.
rewrite -MH.
by split.
Qed.

Lemma jW {T : lattice} : forall a : T, a ⊔ a ≤ a.
Proof.
move=> a.
move: (reflex a)=> H.
rewrite -JH.
by split.
Qed.


Theorem Curry4B_7 {T : lattice} : (forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ c)) 
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite /Distributive => H.
  move=> a b c.
  move: (H a b c) => /siml-H1.
  move: (mab_leq_ab a c) => /proj2 /(RpJ _ _ (a ⊓ b)).
  move: H1.
  apply: trans.
move=> H a b c.
move: (mab_leq_ab a (b ⊔ c)) => /proj1-H0.
move: (conj H0 (H a b c)).
rewrite MH [(a ⊓ b) ⊔ c]L2 => H1.
move: (H a c (a ⊓ b))=> H2.
move: (trans _ _ _ H1 H2).
rewrite [(a ⊓ c) ⊔ (a ⊓ b)]L2 => H3.
move: (Lema4_1i a b c) => H4.
by move: (antisym _ _ H4 H3).
Qed.


(*
  rewrite /Distributive => H.
  move=> a b c.
  have sim:  forall a b : T, a = b -> a ≤ b.
    move=> x y Hip; rewrite Hip; apply: reflex.
  have Hip :forall a b c : T, (a ⊓ b) ⊔ (a ⊓ c) ≤ ((a ⊓ b) ⊔ c).
    move=> x y z.
    rewrite -JH.
    split.
      by move: (ab_leq_jab (x ⊓ y) z ) => /proj1.
    move: (ab_leq_jab (x ⊓ y) z) => /proj2.
    move: (mab_leq_ab x z) => /proj2.
    by apply: trans.
  move: (H a b c) (Hip a b c).
  move=> /sim.
  apply: trans.
move=> H.
have Hip1: forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ (a ⊓ c)).
move=> a b c.
have Hip : forall a b c : T, (a ⊓ ((a ⊓ b) ⊔ c)) ≤ ((a ⊓ b) ⊔ (a ⊓ c)).
  move=> x y z.
  rewrite [(x ⊓ y) ⊔ z]L2 [(x ⊓ y) ⊔ (x ⊓ z)]L2.
  by move: (H x z (x ⊓ y)).
apply: (trans _ (a ⊓ ((a ⊓ b) ⊔ c)) _ ); last first.
 by [].
rewrite -MH.
split; last first.
  by [].
by move: (mab_leq_ab a ((b ⊔ c))) => /proj1.
move=> a b c.
apply: antisym.
  by [].
by move: (Lema4_1i a b c).
Qed.
*)



Theorem Curry4B_9 {T : lattice} : (forall a b c : T, (a ⊓ b ≤ c /\ a ≤ (b ⊔ c)) -> (a ≤ c))
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite -Curry4B_7 => H.
  move=> a b c [H0 H1].
  move: (mW a)=> H2.
  move: (RpM _ _ a H1) => H3.
  move: (trans _ _ _ H2 H3)=> H4.
  move: (trans _ _ _ H4 (H a b c)) => H5.
  move: (RpJ _ _ c H0).
  rewrite L2 => H6.
  move: (trans _ _ _ H6 (jW c)) => H7.
  by move: (trans _ _ _ H5 H7).
move => H.
have aux :forall a b c : T, a ⊓ (b ⊔ c) ≤ ((a ⊓ b) ⊔ c).
move=> a b c.
move: (ab_leq_jab (a ⊓ b) c) => /proj1.
rewrite -{1}(L4d b c) [b ⊓ (b ⊔ c)]L2d -L1d => H0.
move: (mab_leq_ab a (b ⊔ c)) => /proj2.
rewrite -{2}(L4 b a) [b ⊓ a]L2d L1 => H1.
by move: (H _ _ _ (conj H0 H1)).
move: (@Curry4B_7 T) => [Cr Cl].
apply: Cr.
by [].
Qed.

(*
split; last first.
  rewrite -Curry4_7 => H.
  move=> a b c [H0 H1].
  have aux1 : a ⊓ (b ⊔ c) ≤ c.
    apply: (trans _ ((a ⊓ b) ⊔ c)).
      by [].
    rewrite -JH.
    split.
      by [].
    by apply: reflex.
  apply: (trans _ (a ⊓ (b ⊔ c))); last first.
    by [].
  rewrite -MH.
  split; last first.
    by [].
  by apply: reflex.
move=> H.
rewrite -Curry4_7.
move=> a b c.
apply: (H _ b).
  split.
  rewrite L1d [_ ⊓ b]L2d L4d.
  by move: (ab_leq_jab (a ⊓ b) c) => /proj1.
rewrite -L1 [a ⊓ b]L2d L4.
by move: (mab_leq_ab a (b ⊔ c) ) => /proj2. 
Qed.
*)

Lemma Curry4B_91 {T : lattice} : (forall a b c : T, (a ⊓ c ≤ (b ⊓ c) /\ a ⊔ c ≤ (b ⊔ c)) -> (a ≤ b))
                                 <-> (@Distributive T).
Proof.
rewrite -Curry4B_9.
split.
  move => H.
  move => a c b.
  move: (H a b c).
  rewrite -MH -JH [c ⊔ b]L2 => H0 [H1 H3].
  move: (mab_leq_ab a c) => /proj2-H2.
  move: (ab_leq_jab b c) => /proj2-H4.
  apply: H0.
  split.
    by split.
  by split.
move => H a c b.
rewrite -MH -JH.
move=> [[H0 H1] [H2 H3]].
apply: (H a b c).
rewrite [b ⊔ c]L2.
by split.
Qed.

Lemma Curry4B_92 {T : lattice} : (@Distributive T)
                -> (forall a b c : T, (a ⊓ c = (b ⊓ c) /\ a ⊔ c = (b ⊔ c)) -> (a = b)).
Proof.
rewrite -Curry4B_91 => H.
move=> a b c /dobl.
move=> [[/(siml _ _)-H0 /(siml _ _)H1] [/(simr _ _)-H2 /(simr _ _)H3]].
apply: antisym.
apply: (H a b c).
by split.
apply: (H b a c).
by split.
Qed.

Structure implicativeLattice := ImplicativeLattice 
  {
    ImpL :> lattice;
    ply : ImpL -> ImpL -> ImpL;
    Imp_P1 : forall a b : ImpL, a ⊓ (ply a b) ≤ b;
    Imp_P2 : forall a b c : ImpL, a ⊓ c ≤ b -> c ≤ (ply a b)
  }.
Notation "x ⊃ y" := (@ply _ x y) (at level 50). (* \supset *)
Notation P1 := (Imp_P1 _).
Notation P2 := (Imp_P2 _).

(* Sección 4C Curry *)

Theorem Curry4C_LMono {T : implicativeLattice} : forall a b c: T, a ≤ b -> (b ⊃ c) ≤ (a ⊃ c).
Proof.
move=> a b c H.
move: (RpM _ _ (b ⊃ c) H).
rewrite L2d [_⊓ b]L2d => H0.
move: (P1 b c) => H1.
move: (trans _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem Curry4C_RMono {T : implicativeLattice} : forall a b c: T, a ≤ b -> (c ⊃ a) ≤ (c ⊃ b).
Proof.
move=> a b c H1.
move: (P1 c a)=> H0.
move: (trans _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem Curry4C_Unidad {T : implicativeLattice} : forall a : T, exists u, a ≤ u.
Proof.
move=> a.
move: (mab_leq_ab a a) => /proj1.
move=> /P2-H.
by exists (a⊃a).
Qed.

Theorem Curry4C_1i {T : implicativeLattice} : forall a b : T, b ≤ (a ⊃ b).
Proof.
move=> a b.
by move: (mab_leq_ab a b)=> /proj2 /P2.
Qed.

Theorem Curry4C_1ii1 {T : implicativeLattice} 
        : forall a b c : T, (a ⊃ (b ⊃ c) = (a ⊓ b)⊃ c).
Proof.
move=> a b c.
apply antisym.
  move: (P1 a (b ⊃ c)).
  move=> /(RpM _ _ b).
  rewrite -L1d [b ⊓ a]L2d=> H0.
  move: (P1 b c)=> H1.
  move: (trans _ _ _ H0 H1).
  by move=> /P2.
move: (P1 (a ⊓ b) c).
rewrite [_ ⊓ b]L2d L1d.
by move=> /P2 /P2.
Qed.

Theorem Curry4C_1ii2 {T : implicativeLattice} 
        : forall a b c : T, ((a ⊓ b) ⊃ c = b ⊃ (a ⊃ c)).
Proof.
move=> a b c.
move: (Curry4C_1ii1 b a c).
by rewrite L2d.
Qed.

(* Aquí necesito extender la noción de dualidad para que alcance lattices con Top y Bottom *)
(* Dualidad de Bounded Lattice *)

Structure bumcrotLattice := BumcrotLattice 
  {
    BumL :> boundedLattice;
    Mod: (Modu_L BumL)
  }.


Inductive TermB : Set :=
| TopB : TermB
| BotB : TermB
| VarB  : nat -> TermB
| MeetB : TermB -> TermB -> TermB
| JoinB : TermB -> TermB -> TermB.

Fixpoint evalB (L : bumcrotLattice) (env : nat -> L) (t : TermB) : L :=
  match t with
  | TopB        => top
  | BotB        => bot
  | VarB n      => env n
  | MeetB t1 t2 => @meetT L (evalB L env t1) (evalB L env t2)
  | JoinB t1 t2 => @joinT L (evalB L env t1) (evalB L env t2)
  end.

Inductive FormB : Set :=
| fb_leq  : TermB -> TermB -> FormB
| fb_eq   : TermB -> TermB -> FormB
| fb_neg  : FormB -> FormB
| fb_conj : FormB -> FormB -> FormB
| fb_or   : FormB -> FormB -> FormB
| fb_imp  : FormB -> FormB -> FormB.

Notation "x b⊓ y" := (MeetB x y) (at level 48). (* \sqcap *)
Notation "x b⊔ y" := (JoinB x y) (at level 48). (* \sqcup *)
Notation "x b≤ y" := (fb_leq x y) (at level 49).
Notation "x b= y" := (fb_eq x y) (at level 50).
Notation "b~ f" := (fb_neg f) (at level 50).
Notation "x b/\ y" := (fb_conj x y) (at level 50).
Notation "x b\/ y" := (fb_or x y) (at level 50).
Notation "x b-> y" := (fb_imp x y) (at level 50).


Fixpoint evalB_f (L : bumcrotLattice) (env : nat -> L) (f : FormB) : Prop :=
  match f with
  | fb_leq t1 t2 => (evalB L env t1) ≤ (evalB L env t2)
  | fb_eq t1 t2  => (evalB L env t1) = (evalB L env t2)
  | fb_neg f1     => ~ (evalB_f L env f1)
  | fb_conj f1 f2  => evalB_f L env f1 /\ evalB_f L env f2
  | fb_or f1 f2    => (evalB_f L env f1) \/ (evalB_f L env f2)
  | fb_imp f1 f2   =>  (evalB_f L env f1) -> (evalB_f L env f2)
  end.

Fixpoint dualB_t (t : TermB) : TermB :=
  match t with
  | TopB  => BotB
  | BotB  => TopB
  | VarB n => VarB n
  | MeetB t1 t2 => JoinB (dualB_t t1) (dualB_t t2)
  | JoinB t1 t2 => MeetB (dualB_t t1) (dualB_t t2)
  end.

Fixpoint dualB (f : FormB) : FormB :=
  match f with
  | fb_leq t1 t2 => fb_leq (dualB_t t2) (dualB_t t1)
  | fb_eq t1 t2  => fb_eq (dualB_t t1) (dualB_t t2)
  | fb_neg f1     => fb_neg (dualB f1)
  | fb_conj f1 f2  => fb_conj (dualB f1) (dualB f2)
  | fb_or f1 f2    => fb_or (dualB f1) (dualB f2)
  | fb_imp f1 f2   => fb_imp (dualB f1) (dualB f2)
  end.


Canonical Structure dual_bounded_lattice_of (L : boundedLattice) : boundedLattice :=
  BoundedLattice
    (dual_lattice_of L) (Bot L) (Top L)  (fun a => 
      let '(conj Htop Hbot) := Top_Bottom L a in
      conj Hbot Htop) .


Lemma le_dualBound (L : boundedLattice) (x y : L) :
  (ord (dual_bounded_lattice_of L) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Lemma le_dualj (L : boundedLattice) (x y : L) :
  (@joinT (dual_bounded_lattice_of L) x y) = (@meetT L x y).
Proof.
by [].
Qed.

Lemma le_dualm (L : boundedLattice) (x y : L) :
  (@meetT (dual_bounded_lattice_of L) x y) = (@joinT L x y).
Proof.
by [].
Qed.


Lemma modular_dual (L : boundedLattice) (P : Modu_L L) : Modu_L (dual_bounded_lattice_of L).
Proof.
  rewrite /Modu_L.
  move=> p q r.
  rewrite le_dualBound le_dualj le_dualj le_dualm le_dualm.
  by move: ((@Modular2 L P) r q p).
Qed.

Canonical Structure dual_bumcrot_lattice_of (B : bumcrotLattice) : bumcrotLattice :=
  BumcrotLattice
    (dual_bounded_lattice_of B)
    (modular_dual (B) (Mod B)).


Lemma jldmB : forall (L : bumcrotLattice), joinT (dual_bumcrot_lattice_of L) = meetT L.
Proof.
  by [].
Qed.

Lemma mldjB : forall (L : bumcrotLattice), meetT (dual_bumcrot_lattice_of L) = joinT L.
Proof.
  by [].
Qed.

Lemma  evalB_m : forall (L : bumcrotLattice) (env : nat -> L) (t0 t1 : TermB), 
              evalB L env (MeetB t0 t1) = meetT L (evalB L env t0) (evalB L env t1).
Proof. by move=> L0 env0; rewrite /evalB. Qed.

Lemma evalB_j : forall (L : bumcrotLattice) (env : nat -> L) (t0 t1 : TermB), 
              evalB L env (JoinB t0 t1) = joinT L (evalB L env t0) (evalB L env t1).
Proof. by move=> L0 env0; rewrite /evalB. Qed.

Lemma evalB_conj : forall (L : bumcrotLattice) (env : nat -> L) (f0 f1 : FormB), 
                   evalB_f L env (fb_conj f0 f1) = and (evalB_f L env f0) (evalB_f L env f1).
Proof.  by []. Qed.

Lemma dualB_conj : forall (f0 f1 : FormB), dualB (fb_conj f0 f1) = fb_conj (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma evalB_or : forall (L : bumcrotLattice) (env : nat -> L) (f0 f1 : FormB), 
                   evalB_f L env (fb_or f0 f1) = or (evalB_f L env f0) (evalB_f L env f1).
Proof.  by []. Qed.

Lemma dualB_or : forall (f0 f1 : FormB), dualB (fb_or f0 f1) = fb_or (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma evalB_imp : forall (L : bumcrotLattice) (env : nat -> L) (f0 f1 : FormB), 
                   evalB_f L env (fb_imp f0 f1) =(( evalB_f L env f0) -> (evalB_f L env f1)).
Proof. by []. Qed.

Lemma dualB_imp : forall (f0 f1 : FormB), dualB (fb_imp f0 f1) = fb_imp (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma dualB_m : forall t0 t1 : TermB, 
                dualB_t (MeetB t0 t1) = JoinB (dualB_t t0) (dualB_t t1).
Proof.  by move=> t2 t3; rewrite /dualB_t. Qed.

Lemma dualB_j : forall t0 t1 : TermB, 
                dualB_t (JoinB t0 t1) = MeetB (dualB_t t0) (dualB_t t1).
Proof.  by move=> t2 t3; rewrite /dualB_t. Qed.

Theorem eval_dualB (L : bumcrotLattice) (env : nat -> L) (t : TermB) :
  evalB (dual_bumcrot_lattice_of L) env t = evalB L env (dualB_t t).
Proof.
elim t.
  (* TopB *)
  by rewrite /evalB.
  (* BotB *)
  by rewrite /evalB.

  (* VarB n *)
  move=> n0.
  by rewrite {1}/evalB/dualB_t/evalB.
  
  (* MeetB t0 t1*)
  move=> t0 H0 t1 H1.
  rewrite dualB_m (evalB_j L env).
  rewrite (evalB_m (dual_bumcrot_lattice_of L) env).
  by rewrite H0 H1 mldjB.

  (* JoinB t0 t1 *)
  move=> t0 H0 t1 H1.
  rewrite dualB_j (evalB_m L env).
  rewrite (evalB_j (dual_bumcrot_lattice_of L) env).
  by rewrite H0 H1 jldmB.
Qed.

Lemma le_dualB (L : bumcrotLattice) (x y : L) :
  (ord (dual_bumcrot_lattice_of L) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Theorem evalB_dual_f (L : bumcrotLattice) (env : nat -> L) (f : FormB) :
  evalB_f (dual_bumcrot_lattice_of L) env f = evalB_f L env (dualB f).
Proof.
elim f.
  (* Term *)
  move=> t0 t1.
  by rewrite /dualB /evalB_f eval_dualB eval_dualB.
  
  move=> t0 t1.
  by rewrite /dualB /evalB_f eval_dualB eval_dualB.
  
  (* Neg *)
  move=> f0 H0.
  have aux: forall (L : bumcrotLattice) (env : nat -> L) (f0 : FormB), evalB_f L env (fb_neg f0) = ~ (evalB_f L env f0).
    by [].
  have auxd: forall (f0 : FormB), dualB (fb_neg f0) = fb_neg (dualB f0).
    by [].
  rewrite auxd aux aux.
  by rewrite H0.

  (* Conj *)
  move=> f0 H0 f1 H1.
  rewrite dualB_conj evalB_conj evalB_conj.
  by rewrite H0 H1.
  
  (* Or *)
  move=> f0 H0 f1 H1.
  rewrite dualB_or evalB_or evalB_or.
  by rewrite H0 H1.
  
  (* Imp *)
  move=> f0 H0 f1 H1.
  rewrite dualB_imp evalB_imp evalB_imp.
  by rewrite H0 H1.
Qed.


Lemma dualB_td : forall t : TermB, t = dualB_t (dualB_t t).
Proof.
move=> t; elim t.
  
  by rewrite /dualB_t.
  
  by rewrite /dualB_t.

  by rewrite /dualB_t.
  
  move=> t0 H0 t1 H1.
  by rewrite dualB_m dualB_j -H0 -H1.
  
  move=> t0 H0 t1 H1.
  by rewrite dualB_j dualB_m -H0 -H1.
Qed.

Lemma dualBd : forall F : FormB, F = dualB (dualB F).
Proof.
move=>F; elim F.
  by move=> t0 t1; rewrite /dualB {1}(dualB_td t0) {1}(dualB_td t1).

  by move=> t0 t1; rewrite /dualB {1}(dualB_td t0) {1}(dualB_td t1).

  by move=> F0 H0; rewrite {1}H0 {3 4}/dualB.

  by move=> F0 H0 F1 H1; rewrite dualB_conj dualB_conj -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dualB_or dualB_or -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dualB_imp dualB_imp -H0 -H1.
Qed.



Definition TeoremaB (F : FormB) : Prop :=
forall (L : bumcrotLattice) (env : nat -> L), (evalB_f L env F).

Theorem DualidadB : forall f : FormB, (TeoremaB f) -> (TeoremaB (dualB f)).
Proof.
move=> f.
elim f.
  move=> t0 t1.

    (* Caso: leq *)

    rewrite /dualB /TeoremaB => Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    by rewrite evalB_dual_f /dualB.

    (* Caso: eq *)
    
    rewrite /TeoremaB /dualB /evalB_f => t0 t1 Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    by rewrite eval_dualB eval_dualB.

    (* Caso: neg *)
    rewrite /TeoremaB => f0 _ Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    have aux: forall (L : bumcrotLattice) (env : nat -> L) (f0 : FormB), evalB_f L env (fb_neg f0) = ~ (evalB_f L env f0).
      by [].
    have auxd: forall (f0 : FormB), dualB (fb_neg f0) = fb_neg (dualB f0).
      by [].
    rewrite auxd aux aux.
    by rewrite evalB_dual_f.

    (* Caso: Conj *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    rewrite dualB_conj evalB_conj evalB_conj.
    by rewrite evalB_dual_f evalB_dual_f.

    (* Caso: Or *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    rewrite dualB_or evalB_or evalB_or.
    by rewrite evalB_dual_f evalB_dual_f.

    (* Caso: Imp *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L env.
    move: (Hip (dual_bumcrot_lattice_of L) env).
    rewrite dualB_imp evalB_imp evalB_imp.
    by rewrite evalB_dual_f evalB_dual_f.
Qed.
(*    Fin del Teorema de dualidad para lattices acotadas     *)

Lemma DualB : forall f : FormB, (TeoremaB f) <-> (TeoremaB (dualB f)).
Proof.
move=> f.
split.
  by move: (DualidadB f).
move: (DualidadB (dualB f))=> H.
by rewrite {2}(dualBd f).
Qed.




Section Bumcrot.



Theorem Bumcrot1 {L : bumcrotLattice} : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> (exists ca, (Comp a ca)) /\ (exists cb, (Comp b cb)).
Proof.
move=> a b caub canb [H0 H1] [H2 H3].
split.
  exists (caub ⊔ (canb ⊓ b)).
  split.
    move: ((Mod L))=> Modu.
    rewrite -(L4 a b).
    rewrite L1 -[_⊔ (caub ⊔ _)]L1 [_⊔ caub]L2.
    rewrite [(caub ⊔ _) ⊔ _]L1 -L1.
    move: (mab_leq_ab a b)=> /proj2.
    move=> /(Modu _ canb)-HMod1.
    rewrite HMod1.
    rewrite H2 [_ ⊓ b]L2d amTop.
    by rewrite L2 -L1 [b ⊔ a]L2 H0.
  move: (@Modular2 L (Mod L))=> Mod2.
  rewrite -(L4d a b).
  have aux : canb ⊓ b ≤ (a ⊔ b).
    move: (ab_leq_jab a b)=>/proj2-Haub.
    move: (mab_leq_ab canb b)=>/proj2-Hb.
    by move: (trans _ _ _ Hb Haub).
  move: aux => /(Mod2 _ caub)-HMod2. 
  rewrite L1d HMod2 H1.
  rewrite L2 ajBot.
  by rewrite [_ ⊓ b]L2d -L1d H3.
exists (caub ⊔ (canb ⊓ a)).
split.
  move: (Mod L)=> Mod.
  rewrite -(L4 b a).
  rewrite L1 -[_⊔ (caub ⊔ _)]L1 [_⊔ caub]L2.
  rewrite [(caub ⊔ _) ⊔ _]L1 -L1.
  move: (mab_leq_ab b a)=> /proj2.
  move=> /(Mod _ canb)-HMod1.
  rewrite HMod1.
  rewrite [b ⊓ _]L2d H2 [_ ⊓ a]L2d amTop.
  by rewrite L2 -L1 H0.
move: (@Modular2 L (Mod L))=> Mod2.
rewrite -(L4d b a) [b ⊔ a]L2.
have aux : canb ⊓ a ≤ (a ⊔ b).
  move: (ab_leq_jab a b)=>/proj1-Haub.
  move: (mab_leq_ab canb a)=>/proj2-Ha.
  by move: (trans _ _ _ Ha Haub).
move: aux => /(Mod2 _ caub)-HMod2. 
rewrite L1d HMod2 H1.
rewrite L2 ajBot.
by rewrite L2d L1d L2d H3.
Qed.

Theorem AuxBumcrot {L : bumcrotLattice} : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> ((Comp a (caub ⊔ (canb ⊓ b)) ) /\ (Comp b (caub ⊔ (canb ⊓ a)))).
Proof. 
move=> a b caub canb [H0 H1] [H2 H3].
move: (Mod L) (@Modular2 L (Mod L))=> Modu Modu2.
split.
  split.
    rewrite -(L4 a b).
    rewrite L1 -[_⊔ (caub ⊔ _)]L1 [_⊔ caub]L2.
    rewrite [(caub ⊔ _) ⊔ _]L1 -L1.
    move: (mab_leq_ab a b)=> /proj2.
    move=> /(Modu _ canb)-HMod1.
    rewrite HMod1.
    rewrite H2 [_ ⊓ b]L2d amTop.
    by rewrite L2 -L1 [b ⊔ a]L2 H0.
  rewrite -(L4d a b).
  have aux : canb ⊓ b ≤ (a ⊔ b).
    move: (ab_leq_jab a b)=>/proj2-Haub.
    move: (mab_leq_ab canb b)=>/proj2-Hb.
    by move: (trans _ _ _ Hb Haub).
  move: aux => /(Modu2 _ caub)-HMod2. 
  rewrite L1d HMod2 H1.
  rewrite L2 ajBot.
  by rewrite [_ ⊓ b]L2d -L1d H3.
split.
  rewrite -(L4 b a).
  rewrite L1 -[_⊔ (caub ⊔ _)]L1 [_⊔ caub]L2.
  rewrite [(caub ⊔ _) ⊔ _]L1 -L1.
  move: (mab_leq_ab b a)=> /proj2.
  move=> /(Modu _ canb)-HMod1.
  rewrite HMod1.
  rewrite [b ⊓ _]L2d H2 [_ ⊓ a]L2d amTop.
  by rewrite L2 -L1 H0.
rewrite -(L4d b a) [b ⊔ a]L2.
have aux : canb ⊓ a ≤ (a ⊔ b).
  move: (ab_leq_jab a b)=>/proj1-Haub.
  move: (mab_leq_ab canb a)=>/proj2-Ha.
  by move: (trans _ _ _ Ha Haub).
move: aux => /(Modu2 _ caub)-HMod2. 
rewrite L1d HMod2 H1.
rewrite L2 ajBot.
by rewrite L2d L1d L2d H3.
Qed.


Theorem AuxBumcrotd {L : bumcrotLattice} : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> ((Comp a (canb ⊓ (caub ⊔ b)) ) /\ (Comp b (canb ⊓ (caub ⊔ a)))).
Proof.
move=> a b caub canb.
(*Por Dualidad*)
have teo : TeoremaB ( 
                      (VarB 0 b⊔ VarB 1) b⊔ VarB 2 b= TopB b/\
                      ((VarB 0 b⊔ VarB 1) b⊓ VarB 2 b= BotB) b->
                      ((VarB 0 b⊓ VarB 1) b⊔ VarB 3 b= TopB) b/\
                      ((VarB 0 b⊓ VarB 1) b⊓ VarB 3 b= BotB) b->
                      (VarB 0 b⊔ (VarB 2 b⊔ (VarB 3 b⊓ VarB 1)) b= TopB b/\
                       (VarB 0 b⊓ (VarB 2 b⊔ (VarB 3 b⊓ VarB 1)) b= BotB)) b/\
                       (VarB 1 b⊔ (VarB 2 b⊔ (VarB 3 b⊓ VarB 0)) b= TopB) b/\
                       (VarB 1 b⊓ (VarB 2 b⊔ (VarB 3 b⊓ VarB 0)) b= BotB)
                      ).




(*
( (((VarB 0 b⊔ VarB 1) b⊔ VarB 2 b= TopB) b/\ ((VarB 0 b⊔ VarB 1) b⊓ VarB 2 b= BotB)) b->
                            (((VarB 0 b⊓ VarB 1) b⊔ VarB 3 b= TopB) b/\ ((VarB 0 b⊓ VarB 1) b⊓ VarB 3 b= BotB)) b->
                            (( (VarB 0 b⊔ (VarB 2 b⊔ (VarB 3 b⊓ VarB 1)) b= TopB) b/\
                             (VarB 0 b⊓ (VarB 2 b⊔ (VarB 3 b⊓ VarB 1)) b= BotB) ) b/\
                             ((VarB 1 b⊔ (VarB 2 b⊔ (VarB 3 b⊓ VarB 0)) b= TopB) b/\
                             (VarB 1 b⊓ (VarB 2 b⊔ (VarB 3 b⊓ VarB 0)) b= BotB)  )))
*)
  rewrite /TeoremaB/evalB_f/evalB => L0 env.
  move: ((@AuxBumcrot L0) (env 0) (env 1) (env 2) (env 3)).
  rewrite /Comp.
  by [].
move: teo; rewrite /transF/transE Dual/dual/dual_t.
rewrite /Teorema => /(_ T (@env_abc T a b c)).
by rewrite /eval_f/eval/env_abc.


move=> a b caub canb [H0 H1] [H2 H3].
split.
  split.
    move: (Mod L)=> /ModularD => ModD.
    rewrite -(L4 a b).
    have aux : (a ⊓ b) ≤ (caub ⊔ b).
      move: (mab_leq_ab a b)=> /proj2-H0b.
      move: (ab_leq_jab caub b)=> /proj2-H1b.
      by move: (trans _ _ _ H0b H1b).
    move: aux => /(ModD _ canb)=>Mod1.
    rewrite L1 Mod1 H2.
    rewrite L2d amTop.
    by rewrite [_ ⊔ b]L2 -L1 H0.
  move: (Mod L)=> /ModularD/ModularD2-ModD.
  rewrite -(L4d a b).
  rewrite L1d -[_ ⊓ (canb ⊓ _)]L1d [_ ⊓ canb]L2d.
  rewrite [(canb ⊓ _) ⊓ _]L1d.
  move: (ab_leq_jab a b)=> /proj2.
  move=> /(ModD _ caub)=> HModD1.
  rewrite HModD1 H1.
  rewrite L2 ajBot.
  by rewrite [_ ⊓ b]L2d -L1d H3.
split.
  move: (Mod L)=> /ModularD => ModD.
  rewrite -(L4 b a).
  have aux: (b ⊓ a) ≤ (caub ⊔ a).
    move: (mab_leq_ab b a)=> /proj2-H0a.
    move: (ab_leq_jab caub a)=> /proj2-H1a.
    by move: (trans _ _ _ H0a H1a).
  move: aux => /ModD-HModD.
  rewrite L1 HModD.
  rewrite [_ ⊓ a]L2d H2 L2d amTop.
  by rewrite L2 L1 L2 H0.
move: (Mod L)=> /ModularD/ModularD2-ModD.
rewrite -(L4d b a) [b ⊔ a]L2.
rewrite L1d -[_ ⊓ (canb ⊓ _)]L1d [_ ⊓ canb]L2d.
move: (ab_leq_jab a b)=> /proj1/(ModD _ caub)-HModD.
rewrite L1d HModD.
rewrite H1 [_ ⊔ a]L2 ajBot.
by rewrite L2d L1d L2d H3.
Qed.

Definition C_unico {L : bumcrotLattice} (a : L) := forall b c : L, (Comp a b) /\ (Comp a c) -> b = c.

Variable L : bumcrotLattice.
Variables a b ca cb canb caub : L.
Hypothesis (CompUa : C_unico a) (CompUb : C_unico b) (Comp_a : Comp a ca) (Comp_b : Comp b cb)
           (H0 : Comp (a ⊔ b) caub) (H1 : Comp (a ⊓ b) canb).

Lemma auxCompBumcrot : (ca = caub ⊔ (canb ⊓ b)) /\ (cb = caub ⊔ (canb ⊓ a)).
Proof.
split.
  apply: CompUa.
  split.
    by [].
  move: (AuxBumcrot a b caub canb).
  by move=> /(_ H0)/(_ H1)/proj1.
apply: CompUb.
split.
  by [].
move: (AuxBumcrot a b caub canb).
by move=> /(_ H0)/(_ H1)/proj2.
Qed.

Lemma auxCompBumcrotD : (ca = canb ⊓ (caub ⊔ b) /\ cb = canb ⊓ (caub ⊔ a)).
Proof.
split.
  apply: CompUa.
  split.
    by [].
  move: (AuxBumcrotd a b caub canb).
  by move=> /(_ H0)/(_ H1)/proj1.
apply: CompUb.
split.
  by [].
move: (AuxBumcrotd a b caub canb).
by move=> /(_ H0)/(_ H1)/proj2.
Qed.

Theorem Bumcrot2 : (Comp (a ⊓ b) (ca ⊔ cb)) /\ (Comp (a ⊔ b) (ca ⊓ cb)).
Proof.
move: H0 => [H2 H3].
move: H1 => [H4 H5].
split.
  split.
    move: auxCompBumcrot => [HCa HCb].
    rewrite HCa HCb [_ ⊔ (caub ⊔ _)]L1 -[(canb ⊓ b) ⊔ (caub ⊔ (canb ⊓ a))]L1.
    rewrite [_ ⊔ caub]L2 L1 -[caub ⊔ (caub ⊔ _)]L1.
    rewrite L3 -[_ ⊔ (caub ⊔ _)]L1 [_ ⊔ caub]L2.
    rewrite L1 -[_ ⊔ ((canb ⊓ b) ⊔ _)]L1 -(L3 (a ⊓ b)).
    rewrite L1 [((a ⊓ b) ⊔ (a ⊓ b)) ⊔ _]L1.
    rewrite -[(a ⊓ b) ⊔ ((canb ⊓ b) ⊔ (canb ⊓ a))]L1.
    rewrite [_ ⊔ (canb ⊓ b)]L2 [(_ ⊔ (a ⊓ b)) ⊔ _]L1.
    rewrite -[(a ⊓ b) ⊔ (_ ⊔ _)]L1.
    move: (Mod L); rewrite /Modular => Mod.
    move: (mab_leq_ab a b)=> [A B].
    move: A => /(Mod _ canb)-HModa.
    move: B => /(Mod _ canb)-HModb.
    rewrite HModa HModb H4.
    rewrite L2d [_ ⊓ a]L2d amTop amTop.
    by rewrite L2 [b ⊔ a]L2 H2.
  move: (Mod L)=> /ModularD/ModularD2-ModD.
  move: auxCompBumcrotD => [HCa HCb].
  rewrite HCa HCb.
  move: (mab_leq_ab canb (caub ⊔ a))=> /proj1.
  move=> /(ModD _ (caub ⊔ b))=> HModD.
  rewrite -HModD -L1d H5.
  move: (TB ((caub ⊔ b) ⊔ (canb ⊓ (caub ⊔ a))))=> /proj2.
  by rewrite ConnectM.
split.
  move: (Mod L)=> /ModularD-ModD.
  move: auxCompBumcrot => [HCa HCb].
  rewrite HCa HCb.
  move: (ab_leq_jab caub (canb ⊓ a))=> /proj1.
  move=> /(ModD _ (canb ⊓ b))-HModD.
  rewrite -HModD -L1 H2 L2.
  move: ( TB ((canb ⊓ b) ⊓ (caub ⊔ (canb ⊓ a))))=> /proj1.
  by rewrite ConnectJ.
move: (Mod L)=> /Modular2-Mod.
move: auxCompBumcrotD => [HCa HCb].
rewrite HCa L1d [_ ⊓ cb]L2d -[_ ⊓ (cb ⊓_)]L1d.
rewrite HCb -L1d -[canb ⊓ (canb ⊓ _)]L1d.
rewrite L3d -[(a ⊔ b) ⊓ (canb ⊓ _)]L1d [_ ⊓ canb]L2d.
rewrite L1d L1d -[(a ⊔ b) ⊓ (_ ⊓ _)]L1d -(L3d (a ⊔ b)).
rewrite [(_ ⊓ _) ⊓ (caub ⊔ a)]L1d [(a ⊔ b) ⊓ _]L2d.
rewrite [(_ ⊓ (a ⊔ b)) ⊓ (caub ⊔ b)]L1d.
move: (ab_leq_jab a b)=> [A B].
move: A => /(Mod _ caub)-HModa.
move: B => /(Mod _ caub)-HModb.
rewrite HModa HModb H3. 
rewrite L2 [_ ⊔ b]L2 ajBot ajBot.
by rewrite L2d H5.
Qed.

End Bumcrot.