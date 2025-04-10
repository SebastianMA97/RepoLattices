From mathcomp Require Import all_ssreflect.

Hypotheses (U:Type)

           (A B C D J K T: U -> Prop)
           (Q H G R F: U -> U -> Prop)
           (P: U -> U -> U -> Prop)
           (f s : U -> U)
           (a b : U).

(* Require Import Classical_Pred_Type. *)

Require Import Classical.
 
Lemma A_dob: forall A : Prop, A <-> A/\A.
move=> A.
split.
  move=> H.
  by split.
by move=> /proj1.
Qed.


Theorem Prb1: (forall x, (exists z, F x z) -> (forall y, F x y)) -> (exists x, exists y, F x y) -> exists x, forall w, F x w.
Proof.
intros.
destruct H1.
exists x.
intro.
assert (H0:= H0 x).
eapply H0 in H1.
exact H1.
Qed.

Theorem Prb1MathComp: (forall x, (exists z, F x z) -> (forall y, F x y)) -> (exists x, exists y, F x y) -> exists x, forall w, F x w.
Proof.
move=> H0 [x H1].
apply: (ex_intro _ x).
by move: H1 => /H0.
Qed.

Theorem Prb2: (forall x, exists y, B x -> G x y) <-> (forall x, B x -> exists y, G x y).
Proof.
intros.
split.
- intros.
  destruct (H0 x).
  exists x0.
  apply H2.
  assumption.
- intros.
  assert ( B x \/ ~ B x).
  * exact (classic (B x)).
  * destruct H1.
   + destruct (H0 x).
     assumption.
     exists x0.
     intro.
     assumption.
   + exists x.
     intro.
     contradiction.
Qed.

Theorem Prb2MathComp: (forall x, exists y, B x -> G x y) <-> (forall x, B x -> exists y, G x y).
Proof.
split.
  move=> H0 x Bx.
  move: H0 => /(_ x) [y Hy].
  apply: (ex_intro _ y).
  by apply: Hy.
move=> H0 x.
case (classic (B x)) => H1.
  move: H0 => /(_ x) /(_ H1) [y Gxy].
  by apply: (ex_intro _ y) => H.
by apply: (ex_intro _ x).
Qed.


Theorem prb3: (forall x,( forall y, (exists z, F y z /\ ~ F z x) -> G x y)) -> (~exists x, G x x) -> (forall (z x: U), F a z -> F z a).
Proof.
intros.
assert (forall w, ~ G w w).
- intro w.
  contradict H1.
  exists w.
  assumption.
- assert (H0:=H0 a).
  assert (H0:=H0 a).
  assert ( (exists z, F a z /\ ~ F z a) \/ ~ (exists z, F a z /\ ~ F z a)).
  * exact (classic ((exists z, F a z /\ ~ F z a))).
  * destruct H4.
   + apply H0 in H4.
     destruct H3 with a.
     assumption.
   + assert (forall z,~ (F a z /\ ~ F z a)).
    ++ intro.
       contradict H4.
       exists z0.
       assumption.
   ++ assert(H5:=H5 z).
      assert (~ F a z \/ F z a).
      +++ assert ( F z a \/ ~ F z a).
          ** exact (classic (F z a)).
          ** right.
             destruct H6.
             assumption.
             contradict H5.
             split.
             assumption.
             assumption.
      +++ destruct H6.
          ** contradiction.
          ** assumption.
Qed.

Theorem prb3MathComp: (forall x,( forall y, (exists z, F y z /\ ~ F z x) -> G x y)) -> (~exists x, G x x) -> (forall (z x: U), F a z -> F z a).
Proof.
move=> H0 H1 z x H.
have H2 : forall w, ~ (G w w).
  move=> w.
  apply: (contra_not _ H1) => Gww.
  by apply: (ex_intro _ w).
move: (H0 a a) => /contra_not /(_ (H2 a))-H3.
have H4 : forall z,~ (F a z /\ ~ F z a).
  move=>z0.
  apply: (contra_not _ H3) => Conj.
  by apply: (ex_intro _ z0).
move: (H4 z) => H5.
have H6 : ~ F a z \/ F z a.
  apply: or_intror.
  case (classic (F z a)) => Hcase.
    by [].
  apply: NNPP.
  apply: (contra_not _ H5) => H7.
  by split.
by case H6.
Qed.

Theorem prb4: (forall x, P a x x) -> (forall x y z, P x y z -> P (f x) y (f z)) -> (exists z, P (f a) z (f (f a))).
Proof.
intros.
assert (H3:= H0 (f a)).
apply H1 in H3.
exists (f a).
assumption.
Qed.

Theorem prb4MathComp: (forall x, P a x x) -> (forall x y z, P x y z -> P (f x) y (f z)) -> (exists z, P (f a) z (f (f a))).
Proof.
move=> H0 H1.
move: (H0 (f a)) => /(H1 a (f a) (f a))-H3.
by apply: (ex_intro _ (f a)).
Qed.

Theorem prb5: (forall y, Q b y) -> (forall x y, Q x y -> Q (s x) (s y)) -> (exists z, Q b z /\ Q z (s (s b))).
Proof.
intros.
assert (H3:= H0 (s b)).
exists (s b).
split.
- assumption.
- apply H1 in H3.
  assumption.
Qed.

Theorem prb5MathComp: (forall y, Q b y) -> (forall x y, Q x y -> Q (s x) (s y)) -> (exists z, Q b z /\ Q z (s (s b))).
Proof.
move=> H0 H1.
move: (H0 (s b)).
move=> /A_dob [H2 /H1-H3].
apply: (ex_intro _ (s b)).
by split.
Qed.

Theorem prb6: (forall x, ~((forall y, H y x) \/ T x)) -> (~ exists y, (T y \/ exists x, ~ H x y)) -> ((forall x y, H x y)/\(forall x, ~ T x)).
Proof.
intros.
split.
- intros.
   -- assert (forall y, ~(T y \/ exists x, ~ H x y)).
     --- intro.
         contradict H1.
         exists y0.
         exact H1.
     --- assert (H2:=H2 y).
      + assert ( ~ T y /\ ~ (exists x, ~ H x y)).
       * split.
        ** contradict H2.
           left.
           assumption.
        ** contradict H2.
           right.
           assumption.
       * destruct H3.
         assert (forall x, ~(~ H x y)).
         ** intro.
            contradict H4.
            exists x0.
            assumption.
         ** assert ( H x y \/ ~ H x y).
          *** exact (classic (H x y)).
          *** destruct H6.
            ++ assumption.
            ++ assert (H5:=H5 x).
               contradiction.
- intro.
 assert (H0:=H0 x).
  assert (~ (forall y, H y x) /\ ~ T x).
  -- assert ( (forall y, H y x) \/ ~ (forall y, H y x)).
      * exact (classic ((forall y, H y x))).
      * destruct H2.
         + split.
           ++ contradict H0.
              left.
              assumption.
           ++ contradict H0.
              right.
              assumption.
         + split.
          ++ assumption.
          ++ contradict H0.
              right.
              assumption.
  -- destruct H2.
     assumption.
Qed.

Theorem prb6MathComp: (forall x, ~((forall y, H y x) \/ T x)) -> (~ exists y, (T y \/ exists x, ~ H x y)) -> ((forall x y, H x y)/\(forall x, ~ T x)).
Proof.
move=> H1 H2.
have H3 : forall y, ( ~ T y /\ ~ (exists x, ~ H x y)).
  have H3: (forall y, ~(T y \/ exists x, ~ H x y)).
    move=> y.
    apply: (contra_not _ H2) => H3.
    by apply: (ex_intro _ y).
  move=> y.
  split.
    move: (H3 y).
    apply: contra_not => Ty.
    by apply: or_introl.
  apply: (contra_not _ H2).
  move=> [x H4].
  apply: (ex_intro _ y).
  apply: or_intror.
  by apply: (ex_intro _ x).
have H4 : (forall y, ~ T y) /\ (forall y x: U, H x y).
  split.
    by move=> y; move: (H3 y) => /proj1.
  move=> y x.
  move: (H3 y) => /proj2-H4.
  apply: NNPP.
  apply: (contra_not _ H4) => H5.
  by apply: (ex_intro _ x).
move: H4 => [H5 H6].
by split.
Qed.

Theorem prb7: (exists x y, H x y \/ H y x) -> (~ exists x, H x x) -> (exists (x y: U), ~(x=y)).
Proof.
intros.
destruct H0.
destruct H0.
exists x.
exists x0.
unfold not.
intro.
unfold not in H1.
apply H1.
exists x0.
destruct H0.
  -rewrite H2 in H0.
   assumption.
  -rewrite H2 in H0.
   assumption.
Qed.

Theorem prb7MathComp: (exists x y, H x y \/ H y x) -> (~ exists x, H x x) -> (exists (x y: U), ~(x=y)).
Proof.
move=> [x [y H1]] H2.
apply: (ex_intro _ x).
apply: (ex_intro _ y).
rewrite /not => eq_xy.
move: H2; rewrite /not => H2.
apply: H2.
apply: (ex_intro _ x).
case H1 => H2.
  by rewrite {2}eq_xy.
by rewrite {1}eq_xy.
Qed.


Theorem prb8: (forall x:U, B x <-> x = b) -> (B b /\ (forall (x y: U), B x /\ B y -> x = y )).
Proof.
intros.
assert (H1:=H0 b).
destruct H1.
split.
- apply H2.
  reflexivity.
- intros.
  destruct H3.
  assert (H5:=H0 x).
  assert (H6:=H0 y).
  destruct H5.
  destruct H6.
  apply H5 in H3.
  apply H6 in H4.
  rewrite H3.
  rewrite H4.
  reflexivity.
Qed.

Theorem prb8MathComp: (forall x:U, B x <-> x = b) -> (B b /\ (forall (x y: U), B x /\ B y -> x = y )).
Proof.
move=> H0.
split.
  move: (H0 b) => /proj2-H1.
  apply: H1.
  by reflexivity.
move=> x y [Bx By].
move: (H0 x) => /proj1 /(_ Bx).
move: (H0 y) => /proj1 /(_ By)-H1.
by rewrite -H1.
Qed.