Require Import Arith.
Require Import Max.
Require Import Relation_Operators.
(* Require Import Wellfounded.*)

(* well-foundedness *)
Section Wf_Symmetric_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Notation Symprod := (symprod A B leA leB).
  
  (* if leA and leB are well-founded, then the products of the two
     relations are well-founded *)
  Lemma Acc_symprod :
    forall a:A, Acc leA a -> forall b:B, Acc leB b -> Acc Symprod (a, b).
  Proof.
    (* induction on the well-foundedness of leA *)
    induction 1 as [a _ IHAcc]; intros b H2.
    (* induction on the accessibility of a fixed b in leB *)
    induction H2 as [b1 H3 IHAcc1].
    constructor; intros ab H5.
    (* consider the left and the right of the sym prod *)
    inversion_clear H5; auto.
    (* apply induction hypothesis *)
    apply IHAcc; auto.
    constructor. apply H3.
  Defined.

  Lemma wf_symprod :
    well_founded leA -> well_founded leB -> well_founded Symprod.
  Proof.
    red.
    destruct a.
    apply Acc_symprod; auto.
  Defined. (* CHANGE! *)
End Wf_Symmetric_Product.

(* terms *)

Inductive Term : Set :=
 Var  : nat -> Term |
 Meet : Term -> Term -> Term |
 Join : Term -> Term -> Term.

Fixpoint size (t : Term) {struct t} : nat :=
 match t with
 | Var n => 0
 | Meet t1 t2 => 1 + max (size t1) (size t2)
 | Join t1 t2 => 1 + max (size t1) (size t2)
 end.

Definition size_pair (p : Term * Term) : nat := size (fst p) + size (snd p).

Definition R := symprod _ _ (ltof _ size) (ltof _ size).

Lemma wf_R : well_founded R.
Proof.
apply wf_symprod;
 apply well_founded_ltof.
Defined.

(* alternative Definition of well-founded *)

Inductive Subterm : Term -> Term -> Prop :=
  Meet1 : forall t u, Subterm t (Meet t u) |
  Meet2 : forall t u, Subterm u (Meet t u) |
  Join1 : forall t u, Subterm t (Join t u) |
  Join2 : forall t u, Subterm u (Join t u).

Lemma wf_Subterm : well_founded Subterm.
Proof.
  red. induction a; constructor; inversion 1; assumption.
Defined.

Definition R' := symprod _ _ Subterm Subterm.

Lemma wf_R' : well_founded R'.
Proof.
apply wf_symprod;
 apply wf_Subterm.
Defined.

Require Import Program.

   (*  ---------------------------- Require Export LOSet. --------------------------------- *)

(** printing /*\ %\ensuremath{\sqcap}% *)
(** printing \*/ %\ensuremath{\sqcup}% *)

(** Lattice-ordered sets. They are equivalent to lattices. *)

                                  (* Require Import ACI. *)
(* equality modulo ACI *)

(*
TODO: merge with AC!!
*)

Require Import Arith.
Require Import List.

Inductive Tree : Set :=
  Leaf : nat -> Tree |
  Node : Tree -> Tree -> Tree.

Fixpoint flatten_cat (t x : Tree) {struct t} : Tree :=
  match t with
  | Leaf _     => Node t x
  | Node t1 t2 => flatten_cat t1 (flatten_cat t2 x)
  end.

Fixpoint flatten (t : Tree) : Tree :=
  match t with
  | Leaf _     => t
  | Node t1 t2 => flatten_cat t1 (flatten t2)
  end.

Fixpoint insert (m : nat) (t : Tree) {struct t} : Tree :=
  match t with
  | Leaf n =>
    if le_gt_dec m n then
      Node (Leaf m) (Leaf n)
    else
      Node (Leaf n) (Leaf m)
  | Node (Leaf n) t' =>
    if le_gt_dec m n then
      Node (Leaf m) t
    else
      Node (Leaf n) (insert m t')
  | t => Node (Leaf m) t
  end.

Fixpoint sort (t : Tree) : Tree :=
  match t with
  | Node (Leaf n) t' => insert n (sort t')
  | t => t
  end.

Fixpoint unique_insert (m : nat) (t : Tree) {struct t} : Tree :=
  match t with
  | Leaf n =>
    match Nat.compare m n with 
    | Lt => Node (Leaf m) (Leaf n)
    | Eq => t
    | Gt => Node (Leaf n) (Leaf m)
    end
  | Node (Leaf n) t' =>
    match Nat.compare m n with
    | Lt => Node (Leaf m) t
    | Eq => t
    | Gt => Node (Leaf n) (unique_insert m t')
    end
  | t => Node (Leaf m) t
  end.

Fixpoint unique_sort (t : Tree) : Tree :=
  match t with
  | Node (Leaf n) t' => unique_insert n (unique_sort t')
  | t => t
  end.

Section ACIRewriting.
  Variable A : Set.
  Variable f : A -> A -> A.
  Hypothesis associative : forall x y z : A, f (f x y) z = f x (f y z).
(* compared to ACI: assoc is flipped to bring it in line with Lattice *)
  Hypothesis commutative : forall x y : A, f x y = f y x.
  Hypothesis idempotent : forall x : A, f x x = x.

  Fixpoint evaluate (env : list A) (def : A) (t : Tree) {struct t} : A :=
    match t with
    | Leaf n     => nth n env def
    | Node t1 t2 => f (evaluate env def t1) (evaluate env def t2)
    end.

  Theorem flatten_cat_valid : forall (env : list A) (def : A) (t x : Tree),
    f (evaluate env def t) (evaluate env def x) = evaluate env def (flatten_cat t x).
  Proof.
  induction t; simpl; auto.
  intros t'; rewrite <- IHt1; rewrite <- IHt2.
  symmetry; rewrite <- associative.
  reflexivity.
  Qed.

  Theorem flatten_valid : forall (env : list A) (def : A) (t : Tree),
    evaluate env def t = evaluate env def (flatten t).
  Proof.
  induction t; simpl; auto.
  rewrite <- flatten_cat_valid; rewrite <- IHt2.
  reflexivity.
  Qed.

  Theorem flatten_valid_2 : forall (t t' : Tree) (env : list A) (def : A),
    evaluate env def (flatten t) = evaluate env def (flatten t') ->
    evaluate env def t = evaluate env def t'. 
  Proof.
  intros.
  rewrite flatten_valid; rewrite flatten_valid with (t:=t').
  assumption.
  Qed.

  Theorem insert_valid : forall (env : list A) (def : A) (n : nat) (t : Tree),
    evaluate env def (insert n t) = f (nth n env def) (evaluate env def t).
  Proof.
  induction t; simpl.
  (* Leaf *)
  destruct (le_gt_dec n n0); simpl; auto.
  (* Node *)
  destruct t1; simpl; auto.
    destruct (le_gt_dec n n0); simpl; auto.
    rewrite IHt2.
    repeat rewrite <- associative.
    rewrite (commutative (nth n0 env def)).
    reflexivity.
  Qed.

  Theorem unique_insert_valid : forall (env : list A) (def : A) (n : nat) (t : Tree),
    evaluate env def (unique_insert n t) =  f (nth n env def) (evaluate env def t).
  Proof.
  induction t. simpl.
  (* Leaf *)
  remember (Nat.compare n n0) as cmp; destruct cmp. simpl.
  (* destruct (Nat.compare n n0) as [] _eq. simpl.  auto. *)
    (* Eq *)
    symmetry in Heqcmp.
    pose proof (nat_compare_eq n n0 Heqcmp); subst; auto.
  (* Node *)
  simpl. auto. simpl. auto.
  destruct t1; simpl; auto.
  remember (Nat.compare n n0) as cmp; destruct cmp. simpl.
    (* Eq *)
    symmetry in Heqcmp.
    pose proof (nat_compare_eq n n0 Heqcmp). subst.
    rewrite <- associative.
    rewrite idempotent.
    reflexivity.
    (* Gt *)
    simpl. auto. simpl.
    rewrite IHt2.
    repeat rewrite <- associative.
    rewrite (commutative (nth n0 env def)).
    reflexivity.
  Qed.

  Theorem sort_valid : forall (env : list A) (def : A) (t : Tree),
    evaluate env def (sort t) = evaluate env def t.
  Proof.
  induction t; auto.
  destruct t1; simpl; auto.
  rewrite insert_valid.
  rewrite IHt2.
  reflexivity.
  Qed.

  Theorem sort_valid_2 : forall (env : list A) (def : A) (t1 t2 : Tree),
    evaluate env def (sort t1) = evaluate env def (sort t2) ->
    evaluate env def t1 = evaluate env def t2.  
  Proof.
  intros.
  rewrite <- sort_valid with (t:=t1); rewrite <- sort_valid with (t:=t2).
  assumption.
  Qed.

  Theorem unique_sort_valid : forall (env : list A) (def : A) (t : Tree),
    evaluate env def (unique_sort t) = evaluate env def t.  
  Proof.
  induction t; auto.
  destruct t1; simpl; auto.
  rewrite unique_insert_valid.
  rewrite IHt2.
  reflexivity.
  Qed.

  Theorem unique_sort_valid_2 : forall (env : list A) (def : A) (t1 t2 : Tree),
    evaluate env def (unique_sort t1) = evaluate env def (unique_sort t2) ->
    evaluate env def t1 = evaluate env def t2.  
  Proof.
  intros.
  rewrite <- unique_sort_valid with (t:=t1); rewrite <- unique_sort_valid with (t:=t2).
  assumption.
  Qed.
End ACIRewriting.

Ltac variables f env t :=
  match t with
  | (f ?X1 ?X2) =>
    let env' := variables f env X2 in variables f env' X1
  | ?X => constr:(cons X env)
  end.

Ltac rank env n v :=
  match env with
  | (cons ?X1 ?X2) =>
    let env' := constr:(X2) in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => rank env' (S n) v
    end
  end.

Ltac reflect env f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := reflect env f X1 with r2 := reflect env f X2 in
      constr:(Node r1 r2)
  | ?X1 => let n := rank env 0 X1 in constr:(Leaf n)
  | _ => constr:(Leaf 0)
  end.

(*
Print flatten_valid_A_2.
Print sort_eq_2.
*)

Ltac A_reflexive A f assoc_thm :=
  match goal with
  | [ |- (?X1 = ?X2 :>A) ] =>
    let env := variables f (nil (A:=A)) X1 in
    let term1 := reflect env f X1 
    with term2 := reflect env f X2 in
    (change (evaluate A f env X1 term1 = evaluate A f env X1 term2);
     apply flatten_valid_2 with (1 := assoc_thm);
     auto)
  end.

Ltac AC_reflexive A f assoc_thm comm_thm :=
  match goal with
  | [ |- (?X1 = ?X2 :>A) ] =>
    let env := variables f (nil (A:=A)) X1 in
    let term1 := reflect env f X1 
    with term2 := reflect env f X2 in
    (change (evaluate A f env X1 term1 = evaluate A f env X1 term2);
     apply flatten_valid_2 with (1 := assoc_thm);
     apply sort_valid_2 with(1 := assoc_thm)  (2 := comm_thm); 
     auto)
  end.

Ltac ACI_reflexive A f assoc_thm comm_thm idem_thm :=
  match goal with
  | [ |- (?X1 = ?X2 :>A) ] =>
    let env := variables f (nil (A:=A)) X1 in
    let term1 := reflect env f X1 
    with term2 := reflect env f X2 in
    (change (evaluate A f env X1 term1 = evaluate A f env X1 term2);
     apply flatten_valid_2 with (1 := assoc_thm);
     apply unique_sort_valid_2 with(1 := assoc_thm)  (2 := comm_thm) (3:=idem_thm); 
     auto)
  end.

(*
Eval lazy in
  (sort_Tree (flatten (node (leaf 0) (node (node (leaf 1) (leaf 2)) (leaf 1))))).

Tree_A A meet v x
  (sort_Tree
     (flatten (node (leaf 0) (node (node (leaf 1) (leaf 2)) (leaf 1))))) =
Tree_A A meet v x
  (sort_Tree (flatten (node (leaf 0) (node (leaf 1) (leaf 2)))))
*)

         (* ------------------------- Termina ACI ------------------------- *)
 (* ---------------------- Require Export Order. -------------------------------- *)

Require Import Setoid.
(* Several proofs rest on rewriting using Setoid equality. *)


Class Order (A : Set) := {
  le : A -> A -> Prop;
  reflexive : forall a, le a a;
  antisymmetric : forall a b, le a b /\ le b a -> a = b;
  transitive : forall a b c, le a b /\ le b c -> le a c}.
Generalizable Variable A.

(** * Notation *)

Infix "<=" := le : order_scope.

Open Scope order_scope.

Notation "x < y" := (x <= y /\ x <> y) (at level 70, no associativity) : order_scope.
(*
Notation "x >= y" := (y <= x) (at level 70, no associativity) : order_scope.
Notation "x > y" := (y <= x /\ x <> y) (at level 70, no associativity) : order_scope.
*)

(* re-open scope so that subsequent definitions see the new notations. *)
Open Scope order_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : order_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : order_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : order_scope.
Notation "x < y < z" := (x < y /\ y < z) : order_scope.

(** The covering relation. *)

Definition covers `{o : Order A} (x y : A)  := forall z, x <= z /\ z < y -> z = x.

Infix "-<" := covers (at level 70, no associativity) : order_scope.

Open Scope order_scope.
(* Print Scopes. *)

Section OrderTheory.
  Context `{o : Order A}.
(* the backquote also introduces A; {} for implicit arguments *)
  Hint Immediate reflexive antisymmetric transitive.

(*
does not work:
Definition covers x y  := forall z, x <= z /\ z < y -> z = x.

Global Notation "x -< y" := (covers x y) (at level 70, no associativity) : order_scope.

Open Scope order_scope.
*)

(** * Proof principles *)

  Lemma above_below : forall a b, a <= b <= a <-> a = b.
  Proof.
    intuition; subst; auto using antisymmetric.
  Qed.

  Lemma indirect_lte_below : forall a b, (forall x, x <= a -> x <= b) <-> a <= b.
  Proof.
  intuition.
  eauto using transitive.
  Qed.

  Lemma indirect_lte_above : forall a b, (forall x, b <= x -> a <= x) <-> a <= b.
  Proof.
    intuition.
    eauto using transitive.
  Qed.

  Lemma indirect_equality_below : forall a b, (forall x, x <= a <-> x <= b) <-> a = b.
  Proof.
  intros.
  rewrite <- above_below.
  repeat rewrite <- indirect_lte_below.
  intuition; generalize (H x); intuition.
  Qed.

  Lemma indirect_equality_above : forall a b, (forall x, a <= x <-> b <= x) <-> a = b.
  Proof.
  intros; split. 
  (* -> *)
  intro LHS.
  apply antisymmetric.
  generalize (reflexive a).
  generalize (reflexive b).
  generalize (LHS a) (LHS b).
  intuition.
  (* <- *)
  intros RHS x.
  subst.
  tauto.
  Qed.

(** * Infimum and supremum *)

  Definition infimum a b glb := forall x, x <= a /\ x <= b <-> x <= glb.

  Definition supremum a b lub := forall x, a <= x /\ b <= x <-> lub <= x.

(** printing glb1 %\coqdocvar{glb$_1$}% *)
(** printing glb2 %\coqdocvar{glb$_2$}% *)
(** printing lub1 %\coqdocvar{lub$_1$}% *)
(** printing lub2 %\coqdocvar{lub$_2$}% *)
  Lemma infimum_unique : forall a b glb1 glb2,
    infimum a b glb1 -> infimum a b glb2 -> glb1 = glb2.
  Proof.
  intros a b glb1 glb2 H1 H2.
  rewrite <- indirect_equality_below; intro x.
  rewrite <- (H1 x). rewrite (H2 x).
  tauto.
  Qed.

  Lemma infimum_idempotent : forall a, infimum a a a.
  Proof.
  intros a x.
  tauto.
  Qed.

  Lemma infimum_commutative : forall a b c, infimum a b c -> infimum b a c.
  Proof.
  intros a b c H x.
  generalize (H x).
  tauto.
  Qed.

  Lemma supremum_unique : forall a b lub1 lub2,
    supremum a b lub1 -> supremum a b lub2 -> lub1 = lub2.
  Proof.
  intros a b lub1 lub2 H1 H2.
  rewrite <- indirect_equality_above; intro x.
  rewrite <- (H1 x). rewrite (H2 x).
  tauto.
  Qed.

  Lemma supremum_idempotent : forall a, supremum a a a.
  Proof.
  intros a x.
  tauto.
  Qed.

  Lemma supremum_commutative : forall a b c, supremum a b c -> supremum b a c.
  Proof.
  intros a b c H x.
  generalize (H x).
  tauto.
  Qed.

(* TODO: better name. *)

  Lemma redundant_below : forall a a', a <= a' <-> infimum a a' a.
  Proof.
  split.
    red.
    intuition.
    eauto using transitive.
    intro H.
    generalize (proj2 (H a) (reflexive a)).
    tauto.
  Qed.

  Lemma redundant_above : forall a a', a <= a' <-> supremum a a' a'.
  Proof.
  split.
    red.
    intuition.
    eauto using transitive.
    intro H.
    generalize (proj2 (H a') (reflexive a')).
    tauto.
  Qed.

End OrderTheory.

Close Scope order_scope.
(* Print Scopes. *)

Local Open Scope order_scope.

   (* --------------------------- Termina Order -------------------------------*)

   (* ----------------- Require Export Lattice. ----------------------------- *)

Class Lattice (A : Set) := {
  meet : A -> A -> A;
  join : A -> A -> A;

  meet_idempotent : forall a, meet a a = a;
  meet_commutative : forall a b, meet a b = meet b a;
  meet_associative : forall a b c, meet (meet a b) c = meet a (meet b c);
  meet_absorptive : forall a b : A, meet a (join a b) = a;
  
  join_idempotent : forall a, join a a = a;
  join_commutative : forall a b, join a b = join b a;
  join_associative : forall a b c, join (join a b) c = join a (join b c);
  join_absorptive : forall a b : A, join a (meet a b) = a}.
(*Generalizable Variable A.*)

Infix "/*\" := meet (at level 40, left associativity) : lattice_scope.
Infix "\*/" := join (at level 50, left associativity) : lattice_scope.

Local Open Scope lattice_scope.

Section LatticeTheory.
  Context `{l : Lattice A}.
  Hint Immediate meet_idempotent meet_commutative meet_associative meet_absorptive.
  Hint Immediate join_idempotent join_commutative join_associative join_absorptive.

  Lemma lte_meet_join : forall a b, a /*\ b = a <-> a \*/ b = b.
  Proof.
  split; intro H; rewrite <- H.
    rewrite join_commutative.
    rewrite meet_commutative.
    rewrite join_absorptive.
    reflexivity.
    rewrite meet_absorptive.
    reflexivity.
   Qed.

  (** *)

  Definition meet_distributive_l_law := forall x y z, x /*\ (y \*/ z) = (x /*\ y) \*/ (x /*\ z).
  Definition meet_distributive_r_law := forall x y z, (x \*/ y) /*\ z = (x /*\ z) \*/ (y /*\ z).
  Definition join_distributive_l_law := forall x y z, x \*/ (y /*\ z) = (x \*/ y) /*\ (x \*/ z).
  Definition join_distributive_r_law := forall x y z, (x /*\ y) \*/ z= (x \*/ z) /*\ (y \*/ z).

  (** One law implies the other three. *)

  Lemma meet_distributive_l_r : meet_distributive_l_law -> meet_distributive_r_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y z.
  rewrite meet_commutative.
  rewrite meet_distributive_l.
  rewrite meet_commutative.
  rewrite (meet_commutative z y).
  reflexivity.
  Qed.

  Lemma meet_distributive_r_l : meet_distributive_r_law -> meet_distributive_l_law.
  Proof.
  unfold meet_distributive_r_law; intro meet_distributive_r.
  intros x y z.
  rewrite meet_commutative.
  rewrite meet_distributive_r.
  rewrite meet_commutative.
  rewrite (meet_commutative z x).
  reflexivity.
  Qed.

  Lemma join_distributive_l_r : join_distributive_l_law -> join_distributive_r_law.
  Proof.
  unfold join_distributive_l_law; intro join_distributive_l.
  intros x y z.
  rewrite join_commutative.
  rewrite join_distributive_l.
  rewrite join_commutative.
  rewrite (join_commutative z y).
  reflexivity.
  Qed.

  Lemma join_distributive_r_l : join_distributive_r_law -> join_distributive_l_law.
  Proof.
  unfold join_distributive_r_law; intro join_distributive_r.
  intros x y z.
  rewrite join_commutative.
  rewrite join_distributive_r.
  rewrite join_commutative.
  rewrite (join_commutative z x).
  reflexivity.
  Qed.

  Lemma distributive_meet_l_join_l : meet_distributive_l_law -> join_distributive_l_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y z.
  rewrite meet_distributive_l.
  rewrite (meet_commutative (x \*/ y) x).
  rewrite meet_absorptive.
  rewrite (meet_distributive_l_r meet_distributive_l).
  rewrite <- (join_associative x (x /*\ z) (y /*\ z)).
  rewrite join_absorptive.
  reflexivity.
  Qed.

  Lemma distributive_join_l_meet_l : join_distributive_l_law -> meet_distributive_l_law.
  Proof.
  unfold join_distributive_l_law; intro join_distributive_l.
  intros x y z.
  rewrite join_distributive_l.
  rewrite (join_commutative (x /*\ y) x).
  rewrite join_absorptive.
  rewrite (join_distributive_l_r join_distributive_l).
  rewrite <- meet_associative.
  rewrite meet_absorptive.
  reflexivity.
  Qed.

  Definition median_law := forall x y z,
    (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x) = (x \*/ y) /*\ (y \*/ z) /*\ (z \*/ x).

  Definition cancel_law := forall a b c, a /*\ b = c /*\ b /\ a \*/ b = c \*/ b -> a = c.

  Lemma distr_cancel : meet_distributive_l_law -> cancel_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros a b c [Hi Hs].
  rewrite <- (join_absorptive a b).
  rewrite Hi.
  rewrite (distributive_meet_l_join_l meet_distributive_l).
  rewrite Hs.
  rewrite join_commutative.
  rewrite <- (distributive_meet_l_join_l meet_distributive_l).
  rewrite Hi.
  rewrite join_absorptive.
  reflexivity.
  Qed.
End LatticeTheory.


(* ------------------------------- Termina Lattice. ----------------------------- *)


Local Open Scope lattice_scope.
Require Import List.

Class LOSet (A : Set) := {
  order :> Order A;
  lattice :> Lattice A;
  consistent : forall a b, a <= b <-> a /*\ b = a}.
(* Generalizable Variable A. *)

Ltac meet_reflexive A l :=
  ACI_reflexive A (meet (Lattice := l)) (meet_associative (Lattice := l))
                          (meet_commutative (Lattice := l)) (meet_idempotent(Lattice := l)).
Ltac join_reflexive A l :=
  ACI_reflexive A (join (Lattice := l)) (join_associative (Lattice := l))
                          (join_commutative (Lattice := l)) (join_idempotent(Lattice := l)).

Section LOSetTheory.
  Context `{l : LOSet A}.
  Hint Resolve reflexive : order.
  Hint Rewrite meet_idempotent meet_commutative meet_associative meet_absorptive : lattice.

  Lemma meet_is_glb : forall {a b : A}, infimum a b (a /*\ b).
  Proof.
  intros a b x.
  repeat (rewrite consistent).
  split.
    (* -> *)
    intros [Ha Hb].
    rewrite <- meet_associative.
    rewrite Ha.
    assumption.
    (* <- *)
    intro; split.
      rewrite <- H.
      meet_reflexive A lattice.
      rewrite <- H.
      meet_reflexive A lattice.
  Qed.

  Lemma join_is_lub : forall {a b : A}, supremum a b (a \*/ b).
  Proof.
  intros a b x.
  repeat (rewrite consistent; rewrite lte_meet_join).
  split.
  (* -> *)
  intros [Ha Hb].
  rewrite join_associative.
  rewrite Hb.
  rewrite Ha.
  reflexivity.
  (* <- *)
  intro H. split.
    rewrite <- H.
    join_reflexive A lattice.
(*
    rewrite join_associative.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
*)
    rewrite <- H.
    join_reflexive A lattice.
(*
    rewrite join_associative.
    rewrite <- join_associative.
    replace (b \*/ a) with (a \*/ b).
    rewrite join_associative.
    replace (b \*/ (b \*/ x)) with (b \*/ x).
    reflexivity.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
    apply join_commutative.
*)
  Qed.

  Lemma meet_characterization : forall a b c : A, a /*\ b = c <-> infimum a b c.
  Proof.
  intros; split.
    intro.
    rewrite <- H.
    apply meet_is_glb.

    apply infimum_unique.
    apply meet_is_glb.
  Qed.

  Lemma join_characterization : forall a b c : A, a \*/ b = c <-> supremum a b c.
  Proof.
  intros; split.
    intro.
    rewrite <- H.
    apply join_is_lub.

    apply supremum_unique.
    apply join_is_lub.
  Qed.

  Lemma meet_is_lb_l : forall a b : A, a /*\ b <= a.
  Proof.
  intros a b.
  exact (proj1 (proj2 (meet_is_glb (a /*\ b)) (reflexive (a /*\ b)))).
  Qed.

  Lemma meet_is_lb_r : forall a b : A, a /*\ b <= b.
  Proof.
  intros a b.
  exact (proj2 (proj2 (meet_is_glb (a /*\ b)) (reflexive (a /*\ b)))).
  Qed.

  Lemma join_is_ub_l : forall a b : A, a <= a \*/ b.
  Proof.
  intros a b.
  exact (proj1 (proj2 (join_is_lub (a \*/ b)) (reflexive (a \*/ b)))).
  Qed.

  Lemma join_is_ub_r : forall a b : A, b <= a \*/ b.
  Proof.
  intros a b.
  exact (proj2 (proj2 (join_is_lub (a \*/ b)) (reflexive (a \*/ b)))).
  Qed.

  Hint Resolve meet_is_lb_l meet_is_lb_r join_is_ub_l join_is_ub_r : order.

  Lemma meet_mono : forall a a' b b' : A, a <= a' /\ b <= b' -> a /*\ b <= a' /*\ b'.
  Proof.
  intros a a' b b'.
  repeat (rewrite consistent).
  intros [Ha Hb].
  rewrite <- Ha; rewrite <- Hb.
  meet_reflexive A lattice.
(*
  rewrite <- meet_associative.
  replace (a /*\ b /*\ a') with (a /*\ a' /*\ b).
  rewrite Ha.
  rewrite meet_associative.
  rewrite Hb.
  reflexivity.
  rewrite meet_associative.
  replace (a' /*\ b) with (b /*\ a').
  rewrite meet_associative.
  reflexivity.
  apply meet_commutative.
*)
  Qed.

  Lemma join_mono : forall a a' b b' : A, a <= a' /\ b <= b' -> a \*/ b <= a' \*/ b'.
  Proof.
  intros a a' b b'.
  repeat (rewrite consistent; rewrite lte_meet_join).
  intros [Ha Hb].
  rewrite <- Ha; rewrite <- Hb.
  join_reflexive A lattice.
(*
  rewrite <- join_associative.
  replace (a \*/ b \*/ a') with (a \*/ a' \*/ b).
  rewrite Ha.
  rewrite join_associative.
  rewrite Hb.
  reflexivity.
  rewrite join_associative.
  replace (a' \*/ b) with (b \*/ a').
  rewrite join_associative.
  reflexivity.
  apply join_commutative.
*)
  Qed.

  Lemma modular_inequality : forall x y : A, x <= y -> forall a, x \*/ (a /*\ y) <= (x \*/ a) /*\ y.
  Proof.
  intros x y H a.
  pose proof (proj2 (meet_is_glb (a /*\ y)) (reflexive (a /*\ y))).
  apply (proj1 (meet_is_glb (x \*/ a /*\ y))); split.
    apply join_mono; split.
      apply reflexive.
      intuition.
  apply (proj1 (join_is_lub y)); split; intuition.
  Qed.

  Lemma meet_below_join : forall a b : A,
    (a /*\ b) <= (a \*/ b).
  Proof.
    intros.
    rewrite consistent.
    rewrite meet_associative.
    rewrite join_commutative.
    rewrite meet_absorptive.
    reflexivity.
  Qed.
    

  Lemma median_inequality : forall x y z : A,
    (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x) <= (x \*/ y) /*\ (y \*/ z) /*\ (z \*/ x).
  Proof.
  intros x y z.
  set (lhs := (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x)).
  repeat (rewrite <- (meet_is_glb lhs)).
  unfold lhs.
  repeat (rewrite <- (join_is_lub (x \*/ y))).
  repeat (rewrite <- (join_is_lub (y \*/ z))).
  repeat (rewrite <- (join_is_lub (z \*/ x))).
(*
  Proof.
  intros x y z.
  rewrite <- (meet_is_glb ((x \*/ y) /*\ (y \*/ z)) (z \*/ x) ((x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x))).
  rewrite <- (meet_is_glb  (x \*/ y) (y \*/ z) ((x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x))).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (x \*/ y)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (x \*/ y)).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (y \*/ z)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (y \*/ z)).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (z \*/ x)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (z \*/ x)).
*)
(*
no deep backtracking:
  intuition (
      (apply (transitive (b := x)) ||
       apply (transitive (b := y)) ||
      apply (transitive (b := z))); split; auto with order; fail).
*)
  intuition
      (apply transitive with (b := x); split; auto with order; fail) ||
      (apply transitive with (b := y); split; auto with order; fail) ||
      (apply transitive with (b := z); split; auto with order; fail).
(*
The idiom [auto with order; fail] makes sure that the goal is
solved completely.
*)
(*
  apply (transitive (b := x)); split; [apply meet_is_lb_l | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := x)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_l | apply join_is_ub_l].
  apply (transitive (b := z)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := x)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := z)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := z)); split; [apply meet_is_lb_l | apply join_is_ub_l].
*)
  Qed.

  Definition modular_law := forall x y : A, x <= y -> forall a, x \*/ (a /*\ y) = (x \*/ a) /*\ y.

  (** Every distributive lattice is modular. *)

  Lemma distr_modular : meet_distributive_l_law -> modular_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y H a.
  rewrite consistent in H.
  rewrite (meet_distributive_l_r meet_distributive_l).
  rewrite H.
  reflexivity.
  Qed.
End LOSetTheory.

Section LOSetFromOrder.
  Context `{o : Order A}.
(*  Hint Immediate reflexive. *)

  Variable omeet : A -> A -> A.
  Hypothesis meet_is_glb : forall a b, infimum a b (omeet a b).

  Variable ojoin : A -> A -> A.
  Hypothesis join_is_lub : forall a b, supremum a b (ojoin a b).

  Lemma meet_definition : forall a b c, omeet a b = c <-> infimum a b c.
  Proof.
  intros a b c.
  assert (Hi := meet_is_glb a b).
  split; intro H.
    rewrite H in Hi; assumption.
    eapply infimum_unique; eassumption.
  Qed.

 (*
  Class Lattice (A : Set) := {
  meet : A -> A -> A;
  join : A -> A -> A;

  meet_idempotent : forall a, meet a a = a;
  meet_commutative : forall a b, meet a b = meet b a;
  meet_associative : forall a b c, meet (meet a b) c = meet a (meet b c);
  meet_absorptive : forall a b : A, meet a (join a b) = a;
  
  join_idempotent : forall a, join a a = a;
  join_commutative : forall a b, join a b = join b a;
  join_associative : forall a b c, join (join a b) c = join a (join b c);
  join_absorptive : forall a b : A, join a (meet a b) = a}.
  
  *)
  Lemma meet_idempotent_fo : forall a, omeet a a = a.
  Proof.
  intro a.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a a x).
  intuition.
  Qed.

Lemma meet_commutative_fo : forall a b, omeet a b = omeet b a.
Proof.
intros a b.
rewrite <- (indirect_equality_below (o := o)); intro x.
rewrite <- (meet_is_glb a b x).
rewrite <- (meet_is_glb b a x).
intuition.
Qed.

Lemma meet_associative_fo : forall a b c, omeet (omeet a b) c = omeet a (omeet b c).
Proof.
intros a b c.
rewrite <- (indirect_equality_below (o := o)); intro x.
rewrite <- (meet_is_glb (omeet a b) c x).
rewrite <- (meet_is_glb a b x).
rewrite <- (meet_is_glb a (omeet b c) x).
rewrite <- (meet_is_glb b c x).
intuition.
Qed.

Lemma meet_absorptive_fo : forall a b : A, omeet a (ojoin a b) = a.
Proof.
intros a b.
rewrite <- (indirect_equality_below (o := o)); intro x.
rewrite <- (meet_is_glb a (ojoin a b) x).
assert (a <= ojoin a b).
  apply (join_is_lub a b (ojoin a b)).
  apply reflexive.
apply (proj1 (redundant_below (o := o) a (ojoin a b)) H).
Qed.

Lemma join_idempotent_fo : forall a, ojoin a a = a.
Proof.
intro a.
rewrite <- (indirect_equality_above (o := o)); intro x.
rewrite <- (join_is_lub a a x).
intuition.
Qed.

Lemma join_commutative_fo : forall a b, ojoin a b = ojoin b a.
Proof.
intros a b.
rewrite <- (indirect_equality_above (o := o)); intro x.
rewrite <- (join_is_lub a b x).
rewrite <- (join_is_lub b a x).
intuition.
Qed.

Lemma join_associative_fo : forall a b c, ojoin (ojoin a b) c = ojoin a (ojoin b c).
Proof.
  intros a b c.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub (ojoin a b) c x).
  rewrite <- (join_is_lub a b x).
  rewrite <- (join_is_lub a (ojoin b c) x).
  rewrite <- (join_is_lub b c x).
  intuition.
Qed.

Lemma join_absorptive_fo : forall a b : A, ojoin a (omeet a b) = a.
Proof.
  intros a b.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a (omeet a b) x).
  assert (omeet a b <= a).
    apply (meet_is_glb a b (omeet a b)).
    apply reflexive.
  generalize (proj1 (redundant_above (o := o) (omeet a b) a) H x).
  intuition.
Qed.


  Instance lattice_from_order : Lattice A := {
    meet := omeet;
    join := ojoin;
    meet_idempotent := meet_idempotent_fo;
    meet_commutative := meet_commutative_fo;
    meet_associative := meet_associative_fo;
    meet_absorptive := meet_absorptive_fo;

    join_idempotent := join_idempotent_fo;
    join_commutative := join_commutative_fo;
    join_associative := join_associative_fo;
    join_absorptive := join_absorptive_fo}.


(*
  (* meet_idempotent *)
  intro a.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a a x).
  intuition.
  (* meet_commutative *)
  intros a b.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a b x).
  rewrite <- (meet_is_glb b a x).
  intuition.
  (* meet_associative *)
  intros a b c.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb (omeet a b) c x).
  rewrite <- (meet_is_glb a b x).
  rewrite <- (meet_is_glb a (omeet b c) x).
  rewrite <- (meet_is_glb b c x).
  intuition.
  (* meet_absorptive *)
  intros a b.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a (ojoin a b) x).
  assert (a <= ojoin a b).
    apply (join_is_lub a b (ojoin a b)).
    apply reflexive.
  apply (proj1 (redundant_below (o := o) a (ojoin a b)) H).
  (* join_idempotent *)
  intro a.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a a x).
  intuition.
  (* join_commutative *)
  intros a b.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a b x).
  rewrite <- (join_is_lub b a x).
  intuition.
  (* join_associative *)
  intros a b c.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub (ojoin a b) c x).
  rewrite <- (join_is_lub a b x).
  rewrite <- (join_is_lub a (ojoin b c) x).
  rewrite <- (join_is_lub b c x).
  intuition.
  (* join_absorptive *)
  intros a b.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a (omeet a b) x).
  assert (omeet a b <= a).
    apply (meet_is_glb a b (omeet a b)).
    apply reflexive.
  generalize (proj1 (redundant_above (o := o) (omeet a b) a) H x).
  intuition.
  Defined.
*)

(*
Class LOSet (A : Set) := {
  order :> Order A;
  lattice :> Lattice A;
  consistent : forall a b, a <= b <-> a /*\ b = a}.
*)

Lemma consistent_fo : forall a b, a <= b <-> a /*\ b = a.
Proof.
  intros a b.
  rewrite meet_definition.
  rewrite redundant_below.
  intuition.
Qed.
  Instance loset_from_order : LOSet A := {
    order := o;
    lattice := lattice_from_order;
    consistent := consistent_fo}.

(*  (* consistent *)
  intros a b.
  rewrite meet_definition.
  rewrite redundant_below.
  intuition.
  Defined. (*Qed.*)
*)
End LOSetFromOrder.


  (*  ---------------------------- Termina LOSet. --------------------------------- *)

(** printing /*\ %\ensuremath{\sqcap}% *)
(** printing \*/ %\ensuremath{\sqcup}% *)

(** Lattice-ordered sets. They are equivalent to lattices. *)


(* Require Import ACI.*)
(*Require Export Order.*)
Local Open Scope order_scope.
(*Require Export Lattice.*)
Local Open Scope lattice_scope.
Require Import List.

(*Class LOSet (A : Set) := {
  order :> Order A;
  lattice :> Lattice A;
  consistent : forall a b, a <= b <-> a /*\ b = a}.
Generalizable Variable A.*)

Ltac meet_reflexive A l :=
  ACI_reflexive A (meet (Lattice := l)) (meet_associative (Lattice := l))
                          (meet_commutative (Lattice := l)) (meet_idempotent(Lattice := l)).
Ltac join_reflexive A l :=
  ACI_reflexive A (join (Lattice := l)) (join_associative (Lattice := l))
                          (join_commutative (Lattice := l)) (join_idempotent(Lattice := l)).

Section LOSetTheory.
  Context `{l : LOSet A}.
  Hint Resolve reflexive : order.
  Hint Rewrite meet_idempotent meet_commutative meet_associative meet_absorptive : lattice.

  Lemma meet_is_glb : forall {a b : A}, infimum a b (a /*\ b).
  Proof.
  intros a b x.
  repeat (rewrite consistent).
  split.
    (* -> *)
    intros [Ha Hb].
    rewrite <- meet_associative.
    rewrite Ha.
    assumption.
    (* <- *)
    intro; split.
      rewrite <- H.
      meet_reflexive A lattice.
      rewrite <- H.
      meet_reflexive A lattice.
  Qed.

  Lemma join_is_lub : forall {a b : A}, supremum a b (a \*/ b).
  Proof.
  intros a b x.
  repeat (rewrite consistent; rewrite lte_meet_join).
  split.
  (* -> *)
  intros [Ha Hb].
  rewrite join_associative.
  rewrite Hb.
  rewrite Ha.
  reflexivity.
  (* <- *)
  intro H. split.
    rewrite <- H.
    join_reflexive A lattice.
(*
    rewrite join_associative.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
*)
    rewrite <- H.
    join_reflexive A lattice.
(*
    rewrite join_associative.
    rewrite <- join_associative.
    replace (b \*/ a) with (a \*/ b).
    rewrite join_associative.
    replace (b \*/ (b \*/ x)) with (b \*/ x).
    reflexivity.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
    apply join_commutative.
*)
  Qed.

  Lemma meet_characterization : forall a b c : A, a /*\ b = c <-> infimum a b c.
  Proof.
  intros; split.
    intro.
    rewrite <- H.
    apply meet_is_glb.

    apply infimum_unique.
    apply meet_is_glb.
  Qed.

  Lemma join_characterization : forall a b c : A, a \*/ b = c <-> supremum a b c.
  Proof.
  intros; split.
    intro.
    rewrite <- H.
    apply join_is_lub.

    apply supremum_unique.
    apply join_is_lub.
  Qed.

  Lemma meet_is_lb_l : forall a b : A, a /*\ b <= a.
  Proof.
  intros a b.
  exact (proj1 (proj2 (meet_is_glb (a /*\ b)) (reflexive (a /*\ b)))).
  Qed.

  Lemma meet_is_lb_r : forall a b : A, a /*\ b <= b.
  Proof.
  intros a b.
  exact (proj2 (proj2 (meet_is_glb (a /*\ b)) (reflexive (a /*\ b)))).
  Qed.

  Lemma join_is_ub_l : forall a b : A, a <= a \*/ b.
  Proof.
  intros a b.
  exact (proj1 (proj2 (join_is_lub (a \*/ b)) (reflexive (a \*/ b)))).
  Qed.

  Lemma join_is_ub_r : forall a b : A, b <= a \*/ b.
  Proof.
  intros a b.
  exact (proj2 (proj2 (join_is_lub (a \*/ b)) (reflexive (a \*/ b)))).
  Qed.

  Hint Resolve meet_is_lb_l meet_is_lb_r join_is_ub_l join_is_ub_r : order.

  Lemma meet_mono : forall a a' b b' : A, a <= a' /\ b <= b' -> a /*\ b <= a' /*\ b'.
  Proof.
  intros a a' b b'.
  repeat (rewrite consistent).
  intros [Ha Hb].
  rewrite <- Ha; rewrite <- Hb.
  meet_reflexive A lattice.
(*
  rewrite <- meet_associative.
  replace (a /*\ b /*\ a') with (a /*\ a' /*\ b).
  rewrite Ha.
  rewrite meet_associative.
  rewrite Hb.
  reflexivity.
  rewrite meet_associative.
  replace (a' /*\ b) with (b /*\ a').
  rewrite meet_associative.
  reflexivity.
  apply meet_commutative.
*)
  Qed.

  Lemma join_mono : forall a a' b b' : A, a <= a' /\ b <= b' -> a \*/ b <= a' \*/ b'.
  Proof.
  intros a a' b b'.
  repeat (rewrite consistent; rewrite lte_meet_join).
  intros [Ha Hb].
  rewrite <- Ha; rewrite <- Hb.
  join_reflexive A lattice.
(*
  rewrite <- join_associative.
  replace (a \*/ b \*/ a') with (a \*/ a' \*/ b).
  rewrite Ha.
  rewrite join_associative.
  rewrite Hb.
  reflexivity.
  rewrite join_associative.
  replace (a' \*/ b) with (b \*/ a').
  rewrite join_associative.
  reflexivity.
  apply join_commutative.
*)
  Qed.

  Lemma modular_inequality : forall x y : A, x <= y -> forall a, x \*/ (a /*\ y) <= (x \*/ a) /*\ y.
  Proof.
  intros x y H a.
  pose proof (proj2 (meet_is_glb (a /*\ y)) (reflexive (a /*\ y))).
  apply (proj1 (meet_is_glb (x \*/ a /*\ y))); split.
    apply join_mono; split.
      apply reflexive.
      intuition.
  apply (proj1 (join_is_lub y)); split; intuition.
  Qed.

  Lemma meet_below_join : forall a b : A,
    (a /*\ b) <= (a \*/ b).
  Proof.
    intros.
    rewrite consistent.
    rewrite meet_associative.
    rewrite join_commutative.
    rewrite meet_absorptive.
    reflexivity.
  Qed.
    

  Lemma median_inequality : forall x y z : A,
    (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x) <= (x \*/ y) /*\ (y \*/ z) /*\ (z \*/ x).
  Proof.
  intros x y z.
  set (lhs := (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x)).
  repeat (rewrite <- (meet_is_glb lhs)).
  unfold lhs.
  repeat (rewrite <- (join_is_lub (x \*/ y))).
  repeat (rewrite <- (join_is_lub (y \*/ z))).
  repeat (rewrite <- (join_is_lub (z \*/ x))).
(*
  Proof.
  intros x y z.
  rewrite <- (meet_is_glb ((x \*/ y) /*\ (y \*/ z)) (z \*/ x) ((x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x))).
  rewrite <- (meet_is_glb  (x \*/ y) (y \*/ z) ((x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x))).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (x \*/ y)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (x \*/ y)).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (y \*/ z)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (y \*/ z)).
  rewrite <- (join_is_lub ((x /*\ y) \*/ (y /*\ z)) ((z /*\ x)) (z \*/ x)).
  rewrite <- (join_is_lub (x /*\ y) (y /*\ z) (z \*/ x)).
*)
(*
no deep backtracking:
  intuition (
      (apply (transitive (b := x)) ||
       apply (transitive (b := y)) ||
      apply (transitive (b := z))); split; auto with order; fail).
*)
  intuition
      (apply transitive with (b := x); split; auto with order; fail) ||
      (apply transitive with (b := y); split; auto with order; fail) ||
      (apply transitive with (b := z); split; auto with order; fail).
(*
The idiom [auto with order; fail] makes sure that the goal is
solved completely.
*)
(*
  apply (transitive (b := x)); split; [apply meet_is_lb_l | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := x)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := y)); split; [apply meet_is_lb_l | apply join_is_ub_l].
  apply (transitive (b := z)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := x)); split; [apply meet_is_lb_l | apply join_is_ub_r].
  apply (transitive (b := z)); split; [apply meet_is_lb_r | apply join_is_ub_l].
  apply (transitive (b := z)); split; [apply meet_is_lb_l | apply join_is_ub_l].
*)
  Qed.

  Definition modular_law := forall x y : A, x <= y -> forall a, x \*/ (a /*\ y) = (x \*/ a) /*\ y.

  (** Every distributive lattice is modular. *)

  Lemma distr_modular : meet_distributive_l_law -> modular_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y H a.
  rewrite consistent in H.
  rewrite (meet_distributive_l_r meet_distributive_l).
  rewrite H.
  reflexivity.
  Qed.
End LOSetTheory.

Section LOSetFromOrder.
  Context `{o : Order A}.
(*  Hint Immediate reflexive. *)

  Variable omeet : A -> A -> A.
  Hypothesis meet_is_glb : forall a b, infimum a b (omeet a b).

  Variable ojoin : A -> A -> A.
  Hypothesis join_is_lub : forall a b, supremum a b (ojoin a b).

  Lemma meet_definition : forall a b c, omeet a b = c <-> infimum a b c.
  Proof.
  intros a b c.
  assert (Hi := meet_is_glb a b).
  split; intro H.
    rewrite H in Hi; assumption.
    eapply infimum_unique; eassumption.
  Qed.

  Instance lattice_from_order : Lattice A := {
    meet := omeet;
    join := ojoin}.
  (* meet_idempotent *)
  intro a.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a a x).
  intuition.
  (* meet_commutative *)
  intros a b.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a b x).
  rewrite <- (meet_is_glb b a x).
  intuition.
  (* meet_associative *)
  intros a b c.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb (omeet a b) c x).
  rewrite <- (meet_is_glb a b x).
  rewrite <- (meet_is_glb a (omeet b c) x).
  rewrite <- (meet_is_glb b c x).
  intuition.
  (* meet_absorptive *)
  intros a b.
  rewrite <- (indirect_equality_below (o := o)); intro x.
  rewrite <- (meet_is_glb a (ojoin a b) x).
  assert (a <= ojoin a b).
    apply (join_is_lub a b (ojoin a b)).
    apply reflexive.
  apply (proj1 (redundant_below (o := o) a (ojoin a b)) H).
  (* join_idempotent *)
  intro a.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a a x).
  intuition.
  (* join_commutative *)
  intros a b.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a b x).
  rewrite <- (join_is_lub b a x).
  intuition.
  (* join_associative *)
  intros a b c.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub (ojoin a b) c x).
  rewrite <- (join_is_lub a b x).
  rewrite <- (join_is_lub a (ojoin b c) x).
  rewrite <- (join_is_lub b c x).
  intuition.
  (* join_absorptive *)
  intros a b.
  rewrite <- (indirect_equality_above (o := o)); intro x.
  rewrite <- (join_is_lub a (omeet a b) x).
  assert (omeet a b <= a).
    apply (meet_is_glb a b (omeet a b)).
    apply reflexive.
  generalize (proj1 (redundant_above (o := o) (omeet a b) a) H x).
  intuition.
  Defined.

  Instance loset_from_order : LOSet A := {
    order := o;
    lattice := lattice_from_order}.
  (* consistent *)
  intros a b.
  rewrite meet_definition.
  rewrite redundant_below.
  intuition.
  Defined. (*Qed.*)
End LOSetFromOrder.






