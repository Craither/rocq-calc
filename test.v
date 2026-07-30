From Stdlib Require Import Arith.
From Stdlib Require Import List.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.
Require Import calc_no_math_comp.
Require Import calc.

Elpi Command say.
Elpi Accumulate lp:{{
  main [trm F] :-
    coq.say F,
    coq.elaborate-skeleton F {{eqType}} F' ok,
    coq.say F'.
}}.

Goal
  forall a b, (fun c => c * a * b) 3 = (fun c => a * c * b) 3.
Proof.
  intros a b.
  context (c*a) = (a*c).
  apply Nat.mul_comm.
  done.
Qed.

Goal forall a b, (a+b) + 2*(a+b) = (a+b) + 2*(b+a).
Proof.
  intros a b.
  context [in (2*_)] (a+b) = (b+a). 
    apply Nat.add_comm.
  done.
Qed.

Goal forall a b, (a+b) + (a+b) = (a+b) + (b+a).
Proof.
  intros a b.
  context [in X in (_ + X)] (a+b) = (b+a).
  apply Nat.add_comm.
  done.
Qed.

Goal
  forall l,
    [seq [seq i + j + 0  | j <- [:: 0]]  | i <- l] =
    [seq [:: i]  | i <- l].
Proof.
  intro l.
  context (i + j + 0) = (i + j).
    apply Nat.add_0_r.
  simpl.
  context (i + 0) = i.
    apply Nat.add_0_r.
  done.
Qed.

Goal
  forall l,
    fold_left (fun acc i => (acc*i) + (acc*i)) l 0 = fold_left (fun acc i => acc*i + (i*acc)) l 0.
Proof.
  intro l.
  context [in X in ((acc*i) + X)] (acc*i) = (i*acc).
    apply Nat.mul_comm.
  done.
Qed.

Goal
  \sum_(0 <= k < 5) (\prod_(0<= j < 7) ((k + j) + (k + j))) = 
  \sum_(0 <= k < 5) (\prod_(0<= j < 7) ((k + j) + (j+k))).
Proof. 
  context [in X in ((k+j) + X)] (k + j) = (j + k).
    apply Nat.add_comm.
  done.
Qed.

Goal
  \sum_(0 <= i < 6 | (i + 2) == 6) i = 3^2.
Proof.
  context i = (i + 0).
  1,2:apply Logic.eq_sym.
  1,2:apply Nat.add_0_r.
Abort.

Lemma gauss_ex_p2 : forall n, \sum_(i < n.+1) (n-i) + \sum_(i<n.+1) i = n.+1 * n.
Proof.
intro n.
rewrite -big_split /=.
context (n - i + i) = n.
  rewrite subnK.
    by [].
  rewrite -ltnS.
  by [].
rewrite sum_nat_const.
rewrite card_ord.
by[].
Qed.


Import Nat.
Lemma test3 a b c d : (a + b) * (c + d) = (a * c + a * d + b * c + b * d).
Proof.
step ((a+b) * _ = (a+b)*c + (a+b)*d).
  now apply mul_add_distr_l.
context ((a+b)*c) = (a*c + b*c).
  now apply mul_add_distr_r.
context ((a+b)*d) = (a*d + b*d).
  now apply mul_add_distr_r.
step (_ = a*c + b*c + a*d + b*d).
  now apply add_assoc.
context (a*c + b*c + a*d) = (a*c + (b*c + a*d)).
  apply eq_sym.
  now apply add_assoc.
context (b*c + a*d) = (a*d + b*c).
  now apply add_comm.
context (a*c + (a*d + b*c) ) = ( a*c + a*d + b*c).
  now apply add_assoc.
done.
Qed.

Lemma rem_id a b : (a+b)^2 = a^2 + b^2 + 2*(a*b).
Proof.
step (_ = (a+b)*(a+b)).
  now apply pow_2_r.
step (_ = (a+b)*a + (a+b)*b).
  now apply mul_add_distr_l.
context ((a+b)*a) = (a*a + b*a).
  now apply mul_add_distr_r.
context ((a+b)*b) = (a*b + b*b).
  now apply mul_add_distr_r.
step (_ = a*a + b*a + a*b + b*b).
  now apply add_assoc.
context (a*a) = (a^2).
  apply eq_sym.
  now apply pow_2_r.
context (b*a) = (a*b).
  now apply mul_comm.
context (a^2 + a*b + a*b ) = ( a^2 + (a*b + a*b)).
  apply eq_sym.
  now apply add_assoc.
context (a*b + a*b) = ( 2*(a*b)).
  apply f_equal2 with (f:=plus).
  trivial.
  apply eq_sym.
  apply Nat.add_0_r.
context (b*b ) = ( b^2).
  apply eq_sym.
  now apply pow_2_r.
step (_ = a^2 + (2*(a*b) + b^2)).
  apply eq_sym.
  now apply add_assoc.
context (2*(a*b) + b^2 ) = ( b^2 + 2*(a*b)).
  now apply add_comm.
step (_ = a^2 + b^2 + 2*(a*b)).
  now apply add_assoc.
done.
Qed.

Open Scope nat_scope.

Lemma test4 a b c : ((2 * (a * b + b * c + c * a)) <= ((a + b + c) ^2))%coq_nat.
Proof.
step (_ = 2*(a*b) + 2*(b*c) + 2*(c*a)).
Show Proof.
  step (_ = 2*(a*b + b*c) + 2*(c*a)).
    now apply mul_add_distr_l.
  apply f_equal2 with (f:=plus).
  2:trivial.
  now apply mul_add_distr_l.
step  (_ <= a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(c*a))%coq_nat.
  step  (2*(a*b) + 2*(b*c) + 2*(c*a) <= 2*(a*b) + 2*(b*c) + 2*(c*a) + (a^2 + b^2 + c^2))%coq_nat.
    now apply le_add_r.
  step (_ = a^2 + b^2 + c^2 + (2*(a*b) + 2*(b*c) + 2*(c*a))).
    now apply add_comm.
  context (2*(a*b) + 2*(b*c) + 2*(c*a) ) = ( 2*(a*b) + (2*(b*c) + 2*(c*a))).
    apply eq_sym.
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + (2*(b*c) + 2*(c*a))).
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(c*a)).
    now apply add_assoc.
  done.
step (_ = (a + b + c)^2).
  apply eq_sym.
  step ((a+b+c)^2 = (a+b)^2 + c^2 + 2*((a+b)*c)).
    now apply rem_id.
  context ((a+b)^2 ) = ( a^2 + b^2 + 2*(a*b)).
    now apply rem_id.
  context ((a+b)*c ) = ( a*c + b*c).
    now apply mul_add_distr_r.
  context (2*(a*c + b*c) ) = ( 2*(a*c) + 2*(b*c)).
    now apply mul_add_distr_l.
  step (_ = a^2 + b^2 + 2*(a*b) + c^2 + 2*(a*c) + 2*(b*c)).
    now apply add_assoc.
  context (a^2 + b^2 + 2*(a*b) + c^2 ) = ( a^2 + b^2 + (2*(a*b) + c^2)).
    apply eq_sym.
    now apply add_assoc.
  context (2*(a*b) + c^2 ) = ( c^2 + 2*(a*b)).
    now apply add_comm.
  context (a^2 + b^2 + (c^2 + 2*(a*b)) ) = ( a^2 + b^2 + c^2 + 2*(a*b)).
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + (2*(a*c) + 2*(b*c))).
    apply eq_sym.
    now apply add_assoc.
  context (2*(a*c) + 2*(b*c) ) = ( 2*(b*c) + 2*(a*c)).
    now apply add_comm.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(a*c)).
    now apply add_assoc.
  context (a*c ) = ( c*a).
    now apply mul_comm.
  done.
done.
Qed.