From mathcomp Require Import all_ssreflect.

Require Import Classical.

Parameters (p q r s t u v w l m n k  C:Prop)
           (A: Set)
           (a:A)
           (P: A -> Prop)
           (R: A -> A -> Prop).



Check classic.

Check classic u.

Check classic (u\/v).

Check NNPP.

Check NNPP v.

Check NNPP (u -> v).



Theorem i: ~(p /\ q) -> p -> (~ q -> r) -> r.
Proof.
intros.
destruct (classic q).
- cut (p/\q).
  intro.
  * contradiction.
  * split.
    assumption.
    assumption.
- apply H1 in H2.
assumption.
Qed.

Theorem iMathComp: ~(p /\ q) -> p -> (~ q -> r) -> r.
Proof.
move=> H H1 H2.
case: (classic q).
  move=> H4.
  suff H3 : (p/\q).
  by [].
  by split.
by [].
Qed.

Theorem j: ~(p /\ ~ (~ q)) -> (~ q -> r) -> (p -> r).
Proof.
intros.
destruct (classic (~ q)).
- apply H0 in H2.
  assumption.
- cut(p/\~(~q)).
  intro.
  * contradiction.
  * split.
    assumption.
    assumption.
Qed.

Theorem jMathComp: ~(p /\ ~ (~ q)) -> (~ q -> r) -> (p -> r).
Proof.
move=> *.
case: (classic (~ q)).
  by [].
move=> NNq. 
suff H : (p/\~(~q)).
by [].
by split.
Qed.


Theorem kk: ~p -> ~q -> ~(p \/ q) \/ r.
Proof.
intros.
left.
unfold not.
intro.
destruct H1.
- contradiction.
- contradiction.
Qed.

Theorem kkMathComp: ~p -> ~q -> ~(p \/ q) \/ r.
Proof.
move=> *.
apply: or_introl.
rewrite /not => H1.
by case: H1.
Qed.

Theorem ll: p \/ q -> ~ q -> ~(~ p \/ q).
Proof.
intros.
unfold not.
intro.
destruct H.
- destruct H1.
  + apply H1 in H.
    assumption.
  + contradiction.
- contradiction.
Qed.

Theorem llMathComp: p \/ q -> ~ q -> ~(~ p \/ q).
Proof.
move=> H0 H1.
rewrite /not => H2.
case: H0.
  by case: H2.
by [].
Qed.


Theorem aa: s<->t -> (r->(s\/t)) -> ~t/\(p\/q) -> (q->r)/\w -> p.
Proof.
intros.
destruct H1.
destruct H2.
destruct H.
destruct H3.
  * assumption.
  * apply H2 in H3.
    apply H0 in H3.
    destruct H3.
    - apply H in H3.
      contradiction.
    - contradiction.
Qed.


Theorem aaMathComp: s<->t -> (r->(s\/t)) -> ~t/\(p\/q) -> (q->r)/\w -> p.
Proof.
move=> [H0 H1] H3 [H4 H5] [H6 H7].
case: H5.
  by [].
move=> /H6 /H3-H.
case: H.
  by move=> /H0.
by [].
Qed.


Theorem bb: p \/ q \/ r -> (r -> ~(~ s)) -> t /\ ~ u -> (q -> w) /\ ~ p -> ((~ u \/ k) -> l) -> l/\(w\/s).
Proof.
intros.
split.
- apply H3.
  left.
  destruct H1.
  assumption.
- destruct H.
  destruct H2.
  + contradiction.
  + destruct H.
    * destruct H2.
      apply H2 in H.
      left.
      assumption.
    * apply H0 in H.
      right.
      exact ((NNPP s) H).
Qed.

Theorem bbMathComp: p \/ q \/ r -> (r -> ~(~ s)) -> t /\ ~ u -> (q -> w) /\ ~ p -> ((~ u \/ k) -> l) -> l/\(w\/s).
Proof.
move=> H0 H1 [H2 H3] [H4 H5] H6.
split.
  apply: H6.
  by apply: or_introl.
case H0.
  by [].
case=> [Q | R].
  apply: or_introl.
  by apply: H4.
apply: or_intror.
apply: (NNPP s).
by apply: H1.
Qed.


Theorem cc: (m -> (~ p \/ t)) -> (~ m -> q) -> (p \/ r) /\ (~ q /\ ~r) -> ~ s \/ t.
Proof.
intros.
right.
destruct H1.
destruct H2.
destruct H1.
- destruct (classic m).
  + apply H in H4.
    destruct H4.
    * contradiction.
    * assumption.
  + apply H0 in H4.
    contradiction.
- contradiction.
Qed.

Theorem ccMathComp: (m -> (~ p \/ t)) -> (~ m -> q) -> (p \/ r) /\ (~ q /\ ~r) -> ~ s \/ t.
Proof.
move=> H0 H1 [H2 [H3 H4]].
apply: or_intror.
case H2; last first.
  by [].
case (classic m).
  move=> /H0.
  by case=> [Np | T].
by move=> /H1.
Qed.


Theorem dd: (p -> (q -> r)) -> (s -> (t /\ u)) -> ((q -> r) -> (p -> s)) -> ((~ p \/ t) -> (q -> r)) -> ~ r -> ~ q /\ ~ r.
Proof.
intros.
split.
- unfold not.
  intro.
  destruct (classic p).
  + apply H in H5.
    * contradiction.
    * assumption.
  + cut (~p \/ t).
    * intros.
      apply H2 in H6.
      ** contradiction.
      ** assumption.
    * left.
      assumption.
- assumption.
Qed.

Theorem ddMathComp: (p -> (q -> r)) -> (s -> (t /\ u)) -> ((q -> r) -> (p -> s)) -> ((~ p \/ t) -> (q -> r)) -> ~ r -> ~ q /\ ~ r.
Proof.
move=> H0 H1 H2 H3 H4.
split; last first.
  by [].
rewrite /not => Q.
case (classic p).
  by move=> /H0 /(_ Q).
move=> Np; move: H3.
have H : (~p \/ t).
  by apply: or_introl.
by move=> /(_ H) /(_ Q).
Qed.


Theorem ee: ((p \/ q) -> (p -> ~ q)) -> ((q /\ ~ r) -> (p /\ q)) -> (~ p -> q) -> p \/ r.
Proof.
intros.
destruct (classic p).
- left.
  assumption.
- apply H1 in H2.
  destruct (classic r).
  -- right.
     assumption.
  -- cut (q /\ ~ r).
     intros.
     * apply H0 in H4.
       destruct H4.
       cut (p \/ q).
       intros.
       left.
       assumption.
       left.
       assumption.
     * split.
       assumption.
       assumption.
Qed.

Theorem eeMathComp: ((p \/ q) -> (p -> ~ q)) -> ((q /\ ~ r) -> (p /\ q)) -> (~ p -> q) -> p \/ r.
Proof.
move=> H0 H1 H2.
case (classic p).
  move=> P.
  by apply: or_introl.
move=> /H2 Q.
apply: or_intror.
case (classic r).
  by [].
move=> Nr.
have Hip1 : (q /\ ~ r).
  by split.
move: H1 => /(_ Hip1) /proj1 P.
have Hip2 : (p \/ q).
  by apply: or_introl.
by move: H0 => /(_ Hip2) /(_ P).
Qed.


Theorem ff: ~(t/\r) -> (p->q)/\(r->s) -> t/\(p\/r) -> ~q<->s -> ~r/\~s.
Proof.
intros.
destruct H0.
destruct H1.
destruct H2.
cut (~t\/~r).
intro.
- destruct H6.
  -- contradiction.
  -- split.
     assumption.
     destruct H4.
      * apply H0 in H4.
        cut (q -> ~s).
        ** intro.
           apply H7 in H4.
           assumption.
        ** unfold not.
           intros.
           apply H5 in H8.
           contradiction.
      * contradiction.
- destruct (classic r).
  -- cut (t /\ r).
    * intro.
      contradiction.
    * split.
      assumption.
      assumption.
  -- right.
     assumption.
Qed.


Theorem ffMathComp: ~(t/\r) -> (p->q)/\(r->s) -> t/\(p\/r) -> ~q<->s -> ~r/\~s.
Proof.
move=> H0 [H1 H2] [H3 H4] [H5 H6].
have Hip1 : (~t\/~r).
  case (classic r) => R.
    case (classic t) => T.
      have Conj : (t /\ r).
        by split.
      by [].
    by apply: or_introl.
  by apply: or_intror.
case Hip1 => Nr.
  by [].
split.
  by [].
case H4; last first.
  by [].
move=> /H1 Q.
by rewrite /not => /H6.
Qed.


Theorem iii: (n/\q)\/(n/\r) -> (s\/p)<->~(s/\k) -> ((q\/p)->~n) -> (r->s) -> ~k.
Proof.
intros.
unfold not.
destruct H0.
intro.
cut (n -> ~ q /\ ~ p).
 * intro.
   destruct H.
   - destruct H.
     apply H5 in H.
     destruct H.
     contradiction.
   - destruct H.
     apply H2 in H6.
     cut(s\/p).
     -- intro.
        apply H0 in H7.
        cut (s/\k).
        --- intro.
            contradiction.
        --- split.
            assumption.
            assumption.
     -- left.
        assumption.
 * intro.
   destruct (classic p).
   - cut (q\/p).
     -- intro.
        apply H1 in H7.
        contradiction.
     -- right.
        assumption.
   - destruct (classic q).
     -- cut (q\/p).
        intros.
        apply H1 in H8.
        contradiction.
        left.
        assumption.
     -- split.
        assumption.
        assumption.
Qed.

Theorem iiiMathComp: (n/\q)\/(n/\r) -> (s\/p)<->~(s/\k) -> ((q\/p)->~n) -> (r->s) -> ~k.
Proof.
move=> H0 [H1 H2] H3 H4.
rewrite /not => K.
have Hip1 : (n -> ~ q /\ ~ p).
  move=> N.
  case (classic p) => P.
    have Hip0 : (q \/ p).
      by apply: or_intror.
    by move: Hip0 => /H3.
  case (classic q) => Q.
    have Hip0 : (q \/ p).
      by apply: or_introl.
    by move: Hip0 => /H3.
  by split.
case H0.
  by move => [/Hip1 [Nq Np] Q].
move => /proj2 /H4-S.
have Hip2: (s \/ p).
  by apply: or_introl.
move: Hip2 => /H1.
have Hip3 : (s /\ k) by split.
by [].
Qed.

Theorem jjj: ((k/\l)->~m) -> (s->(m/\p)) -> (t->(q/\r)) -> l/\(s\/t) -> k<->l -> q\/~l.
Proof.
intros.
destruct H2.
destruct H3.
cut (k/\l).
- intro.
  apply H in H6.
  destruct H4.
  -- apply H0 in H4.
     destruct H4.
     contradiction.
  -- apply H1 in H4.
     destruct H4.
     left.
     assumption.
- split.
  * apply H5 in H2.
    assumption.
  * assumption.
Qed.

Theorem jjjMathComp: ((k/\l)->~m) -> (s->(m/\p)) -> (t->(q/\r)) -> l/\(s\/t) -> k<->l -> q\/~l.
Proof.
move=> H1 H2 H3 [H4 H5] H6.
have Hip1 : (k/\l).
  split.
    by rewrite H6.
  by [].
case H5.
  move=> /H2 [M P].
  by move: Hip1 => /H1.
move=> /H3 [Q R].
by apply: or_introl.
Qed.

Theorem hhhh: (r->(p->q)) -> (r->((p\/q)->q)).
Proof.
intro.
intro.
intro.
destruct H1.
- apply H in H0.
  assumption.
  assumption.
- assumption.
Qed.

Theorem hhhhMathComp: (r->(p->q)) -> (r->((p\/q)->q)).
Proof.
move=> H0 H1 H2.
case H2; last first.
  by [].
by apply: H0.
Qed.

Theorem iiii: ((p/\q)->r) -> ((p/\~q)->s) -> (p->(r\/s)).
Proof.
intro.
intro.
intro.
destruct (classic q).
- cut (p/\q).
  intro.
  * apply H in H3.
    left.
    assumption.
  * split.
    assumption.
    assumption.
- cut (p/\~q).
  intro.
  * apply H0 in H3.
    right.
    assumption.
  * split.
    assumption.
    assumption.
Qed.

Theorem iiiiMathComp: ((p/\q)->r) -> ((p/\~q)->s) -> (p->(r\/s)).
Proof.
move=> H0 H1 H2.
case (classic q) => Q.
  apply: or_introl.
  apply: H0.
  by split.
apply: or_intror.
apply: H1.
by split.
Qed.

Theorem jjjj: (p->q)\/(p->r) -> (q->s) -> (r->s) -> (p->s).
Proof.
intros.
destruct H.
- apply H in H2.
  apply H0 in H2.
  assumption.
- apply H in H2.
  apply H1 in H2.
  assumption.
Qed.

Theorem jjjjMathComp: (p->q)\/(p->r) -> (q->s) -> (r->s) -> (p->s).
Proof.
move=> H0 H1 H2 H3.
case H0.
  by move=> /(_ H3) /H1.
by move=> /(_ H3) /H2.
Qed.

Theorem kkkk: ((p\/q)->~r) -> (s->(~u/\~w)) -> (m->(r/\u)) -> ((p\/s)->~m).
Proof.
intros.
unfold not.
intro.
apply H1 in H3.
destruct H3.
destruct H2.
- cut (p\/q).
  intro.
  * apply H in H5.
    contradiction.
  * left.
    assumption.
- apply H0 in H2.
  destruct H2.
  contradiction.
Qed.

Theorem kkkkMathComp: ((p\/q)->~r) -> (s->(~u/\~w)) -> (m->(r/\u)) -> ((p\/s)->~m).
Proof.
move=> H0 H1 H2 H3.
rewrite /not => /H2 [R U].
case H3; last first.
  by move=> /H1 /proj1.
move=> P.
have Hip : (p\/q).
  by apply: or_introl.
by move: Hip => /H0.
Qed.

