From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


Definition reflexive {T : Type} (rel : T -> T -> Prop) : Prop := forall x :T, rel x x.
Definition antisymetric {T : Type} (rel : T -> T -> Prop) : Prop := forall x y : T, (rel x y) /\ (rel y x) <-> (x = y).
Definition transitive {T : Type} (rel : T -> T -> Prop) :Prop := forall x y z :T, rel x y -> rel y z -> rel x z.

Inductive Term := Var (n : nat) | m (u : Term) (v : Term).

Notation "x ∧ y" := (m x y) (at level 49). (* \wedge *)


Fixpoint atm_en (s : Term) (j : nat) : Prop :=
  match s with
  | Var i => i = j
  | s1 ∧ s2 => atm_en s1 j \/ atm_en s2 j
  end.

Fixpoint leq (s t : Term) : Prop :=
  match t with
  | Var j => atm_en s j
  | t1 ∧ t2 => leq s t1 /\ leq s t2
  end.
Notation "x ≤ y" := (leq x y)(at level 50).

Structure lattice := Lattice
  {
    reflexq : reflexive leq;
    antisymq : antisymetric leq;
    transq : transitive leq;
    LambdaK : forall a b : Term, leq (a ∧ b) a;
    LambdaK' : forall a b : Term, leq (a ∧ b) b;
    LambdaS : forall a b c : Term, (leq c a /\ leq c b ) -> leq c (a ∧ b);
   }.

Variable L : lattice.
Notation ρ := (reflexq L).
Notation τ := (transq L).
Notation σ := (antisymq L).
Notation ΛK := (@LambdaK L).
Notation ΛK' := (@LambdaK' L).
Notation ΛS := (@LambdaS L).

Theorem ΛW : forall a : Term, a ≤ (a ∧ a).
Proof.
move=> a.
move: (ρ a)=> H0.
by move: (conj H0 H0)=> /ΛS.
Qed.

Theorem ΛC : forall a b : Term, a ∧ b ≤ b ∧ a.
Proof.
move=> a b.
move: (ΛK' a b)=> H0.
move: (ΛK a b)=> H1.
by move: (conj H0 H1)=> /ΛS.
Qed.

Theorem ΛB : forall a b c : Term, (a ≤ b) -> c ∧ a ≤ c ∧ b.
Proof.
move=> a b c H.
apply: ΛS.
split.
  by apply: ΛK.
move: (ΛK' c a)=> H0.
by move: (τ _ _ _ H0 H).
Qed.

Theorem ΛB' : forall a b c : Term, (a ≤ b) -> a ∧ c ≤ b ∧ c.
Proof.
move=> a b c H.
move: (ΛB a b c)=> /(_ H)-H0.
move: (ΛC a c)=> H1.
move: (ΛC c b)=> H2.
move: (τ _ _ _ H1 H0)=> H3.
by move: (τ _ _ _ H3 H2).
Qed.


Lemma leqL_atm : forall (n : nat) (s1 s2 : Term),
               (s1 ∧ s2) ≤ Var n <-> atm_en s1 n \/ atm_en s2 n.
Proof.
move=> n s1 s2.
by rewrite /leq /atm_en.
Qed.

Lemma leqR : forall (a t1 t2 : Term), a ≤ (t1 ∧ t2) <-> (a ≤ t1) /\ (a ≤ t2).
Proof.
move=> a t1 t2.
by rewrite /leq.
Qed.

Lemma AtmTerm: forall (n : nat) (a : Term), a ≤ Var n <-> atm_en a n.
Proof.
move=> n a.
by rewrite /leq.
Qed.


Lemma leqL : forall (a b : Term) (n : nat),
           a ∧ b ≤ (Var n) <-> a ≤ (Var n) \/ b ≤ (Var n).
Proof.
move=> a b n.
by rewrite leqL_atm -AtmTerm -AtmTerm.
Qed.


Theorem Teorema2 : forall a b : Term, (forall i : nat, 
            atm_en b i -> atm_en a i) <-> a ≤ b.
Proof.
move=> a b.
split; last first.
  elim b.
    move=> n.
    rewrite AtmTerm => H n0.
    rewrite {1}/atm_en => H0.
    by move: H; rewrite H0.
  move=> u Hu v Hv.
  rewrite leqR.
  move=> [/Hu-H0 /Hv-H1] n0.
  move: (H0 n0) (H1 n0).
  rewrite -AtmTerm -AtmTerm -AtmTerm => H0u H1v.
  rewrite -AtmTerm leqL.
  move=> [U | V].
    by move: U => /H0u.
  by move: V => /H1v.
elim b.
move=> n H.
  rewrite AtmTerm.
  by move: (ρ (Var n)) => /AtmTerm /(H n).
move=> u Hu v Hv Hind.
rewrite leqR.
split.
  apply: Hu.
  move=> n0.
  rewrite -AtmTerm -AtmTerm => H.
  move: (Hind n0).
  rewrite -AtmTerm -AtmTerm leqL => H0.
  have aux : u ≤ Var n0 \/ v ≤ Var n0. 
    by left.
  by move: aux => /H0.
apply: Hv.
move=> n0.
rewrite -AtmTerm -AtmTerm => H.
move: (Hind n0).
rewrite -AtmTerm -AtmTerm leqL => H0.
have aux : u ≤ Var n0 \/ v ≤ Var n0.
by right.
by move: aux => /H0.
Qed.

Theorem C3i : forall a : Term, a ∧ a = a.
Proof.
move=> a.
have aux: forall i : nat, atm_en (a ∧ a) i -> atm_en a i.
  move=> n.
  rewrite -AtmTerm -AtmTerm leqL.
  by case => H.
move: aux (ΛK a a) => /Teorema2-H0 H1.
move: (conj H1 H0).
by rewrite σ.
Qed.


Theorem C3ii : forall a b : Term, a ∧ b = b ∧ a.
Proof.
move=> a b.
move: (ΛC b a)=> H0.
have aux: forall i : nat, atm_en (b ∧ a) i -> atm_en (a ∧ b) i.
  move=> n.
  rewrite -AtmTerm -AtmTerm leqL leqL.
  case => H.
    by right.
  by left.
move: aux => /Teorema2-H1.
move: (conj H0 H1).
by rewrite σ.
Qed.

Theorem C3iii : forall a b c : Term, a ∧ (b ∧ c) = (a ∧ b) ∧ c.
Proof.
move=> a b c.
have aux1: forall i : nat, atm_en (a ∧ (b ∧ c)) i -> atm_en ((a ∧ b) ∧ c) i.
  move=> n.
  rewrite -AtmTerm -AtmTerm leqL leqL.
  rewrite leqL leqL.
  move=> [H0 | [H1 | H2]].
      left.
      by left.
    left.
    by right.
  by right.
have aux2: forall i : nat, atm_en ((a ∧ b) ∧ c) i -> atm_en (a ∧ (b ∧ c)) i.
  move=> n.
  rewrite -AtmTerm -AtmTerm leqL leqL.
  rewrite leqL leqL.
  move=> [[H0 | H1] | H2].
      by left.
    right.
    by left.
  right.
  by right.
move: aux1 aux2 => /Teorema2-H0 /Teorema2-H1.
move: (conj H0 H1).
by rewrite σ.
Qed.


Theorem C3iv : forall a b : Term,
               a ≤ b <-> a = a ∧ b.
Proof.
move=> a b.
split.
  move=> H0.
  move: (ρ a)=> H1.
  move:(conj H1 H0)=> /ΛS-H2.
  move: (ΛK a b) => H3.
  by move: (conj H2 H3) => /σ.
rewrite -σ.
move=> [H0 _].
move: (ΛK' a b) => H1.
by move: (τ _ _ _ H0 H1).
Qed.





