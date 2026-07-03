From Stdlib Require Import Arith.
From Stdlib Require Import List.
From elpi Require Import elpi.
Require Import ssrmatching.

Lemma f_equal_equal:
  forall [A B:Type] [f1 f2: A->B] [x1 x2:A], f1 = f2 -> x1 = x2 -> f1 x1 = f2 x2.
Proof.
  intros A B f1 f2 x1 x2 H1 H2.
  exact (eq_trans (f_equal (fun f : A -> B => f x1) H1) (f_equal f2 H2)).
  Show Proof.
Qed.

Lemma f_equal_relat:
  forall [A B:Type] [f: A->B->Prop] [x y:A] [z:B],
    x = y -> f y z -> f x z.
Proof.
  intros A B f x y z H1 H2.
  apply eq_sym in H1.
  destruct H1.
  assumption.
Qed.

Lemma fold_equal:
  forall [A B:Type] [f g:A->B->A] [l:list B] [i:A],
    (forall [x:A] [y:B],  In y l -> f x y = g x y) -> fold_left f l i = fold_left g l i.
Proof.
  intros A B f g.
  induction l;intros i H1.
  simpl.
  apply eq_refl.
  simpl.
  assert (H: f i a = g i a).
  apply H1.
  simpl.
  apply or_introl.
  apply eq_refl.
  destruct H.
  apply IHl.
  intros x y H'.
  refine (H1 x y _).
  simpl.
  apply or_intror.
  assumption.
Qed.

Lemma map_equal:
  forall [A B:Type] [f g:A->B] [l:list A],
    (forall [x:A], In x l -> f x = g x) -> map f l = map g l.
Proof.
  intros A B f g l H1.
  induction l.
  simpl.
  now apply eq_refl.
  simpl.
  f_equal.
  apply H1.
  simpl.
  apply or_introl.
  reflexivity.
  apply IHl.
  intros x H2.
  apply H1.
  simpl.
  apply or_intror.
  assumption.
Qed.

Elpi Db relations.db lp:{{
  pred trans o:term, o:term, i:term, o:term.
  pred incl o:term, o:term, o:term.
  pred step i:term, i:term, o:term.

  %If we have a direct inclusion between the last goal and the last subgoal,
  %we don't create a new goal
  step E F _ :-
    coq.unify-eq E F ok.
  
  step E F {{lp:IF _}} :-
    incl F E IF.

  %Directly apply one transitivity rule
  step E F {{lp:TF _ _}} :-
    trans F _ E TF.

  step E F {{lp:TF (lp:IF _) _}} :-
    incl F I IF,
    trans I _ E TF.
  
  step E F T :-
    step {whd1 E} {whd1 F} T.

  step _ _ _ :-
    coq.ltac.fail _ "No applicable rule".


  pred step_by_context i:term, i:term, o:term.
  step_by_context E {{lp:Y1 = lp:Y2}} T' :-
    E = app L,
    std.rev L [X2,X1|_],
    (copy Y1 Y2 :-!) ==> copy X1 V,
    step_by_context_aux X1 V Y1 Y2 _ T B,
    if (B = 1) (
      if (trans {{lp:X1 = lp:V}} _ E TF) (
        if (coq.unify-eq X2 V ok) (T' = T) (T' = {{lp:TF lp:T _}})
      ) (
        incl {{lp:X1 = lp:V}} I IF,
        trans I _ E TF,
        if (coq.unify-eq X2 V ok) (T' = {{lp:IF lp:T}}) (T' = {{lp:TF (lp:IF lp:T) _}})
      )
    ) (coq.ltac.fail _ "Pattern not found").

  pred step_by_context_aux i:term, i:term, i:term, i:term, i:term, o:term, o:int.
  step_by_context_aux Y1 Y2 X1 X2 T' T' 1 :-
    coq.unify-eq X1 Y1 ok,
    coq.unify-eq X2 Y2 ok.

  step_by_context_aux X X _ _ _ {{eq_refl lp:X}} 0 :- !.

  step_by_context_aux (app [global (const Map),A,C,F1,L]) (app [global (const Map),A,C,F2,L]) Y1 Y2 T' {{map_equal (fun (x : lp:A) (H : In x lp:L) => lp:{{T {{x}} {{H}}}})}} B :-!,
    coq.locate "map" (const Map),
    @pi-decl _ A x\ (
      @pi-decl _ _ h\ (
        step_by_context_aux {{lp:F1 lp:x}} {{lp:F2 lp:x}} Y1 Y2 T' (T x h) B
      )
    ).

  step_by_context_aux (app [F1|L1]) (app [F2|L2]) Y1 Y2 P' P B :-
    app_rewrite F1 {std.rev L1} F2 {std.rev L2} Y1 Y2 P' P B.

  pred app_rewrite i:term, i:list term, i:term, i:list term, i:term, i:term, i:term, o:term, o:int.
  app_rewrite F1 [] F2 [] Y1 Y2 P' PF B :-
    step_by_context_aux F1 F2 Y1 Y2 P' PF B.

  app_rewrite F1 [X1|L1] F2 [X2|L2] Y1 Y2 P' {{f_equal_equal lp:PF lp:PX}} B' :-
    step_by_context_aux X1 X2 Y1 Y2 P' PX BX,
    app_rewrite F1 L1 F2 L2 Y1 Y2 P' PF BF,
    if (BX = 1) (B' = BX) (B' = BF).
  
  step_by_context_aux X1 X2 Y1 Y2 T' T B :-
    step_by_context_aux {whd1 X1} {whd1 X2} Y1 Y2 T' T B.
}}.

Elpi Command add_transitivity.
Elpi Accumulate Db relations.db.
Elpi Accumulate lp:{{
  func compile term, term -> prop.
  compile (prod _ GL x\ prod _ GR y\ G) P (trans GL GR G P):- !.

  compile {{forall x, lp:(F x) }} P (pi x\ C x) :-!,
    pi x\ compile (F x) {coq.mk-app P [x]} (C x).

  compile T P C :-
    whd1 T T',
    compile T' P C.

  main [trm TF] :- !,
    coq.typecheck TF Ty ok,
    compile Ty TF C,
    coq.elpi.accumulate _ "relations.db" (clause _ _ C).
}}.

Elpi Command add_inclusion.
Elpi Accumulate Db relations.db.
Elpi Accumulate lp:{{
  func compile term, term -> prop.

  compile (prod _ GL x\ GR) P (incl GL GR P):- !.

  compile {{forall x, lp:(F x)}} P (pi x\ C x) :-!,
    pi x\ compile (F x) {coq.mk-app P [x]} (C x).

  compile T P C :-
    whd1 T T',
    compile T' P C.
  
  main [trm IF] :-
    coq.typecheck IF Ty ok,
    compile Ty IF C,
    coq.elpi.accumulate _ "relations.db" (clause _ _ C).
}}.

Lemma eq_le_trans:
  forall x y z:nat, x=y -> y<=z -> x <= z.
Proof.
  intros x y z H1 H2.
  destruct H1.
  assumption.
Qed.

Elpi add_transitivity (eq_trans).
Elpi add_transitivity (Nat.le_trans).
Elpi add_transitivity (Nat.le_lt_trans).
Elpi add_transitivity (Nat.lt_le_trans).

Elpi add_inclusion (Nat.eq_le_incl).
Elpi add_inclusion (Nat.lt_le_incl).

(*Create one subgoal*)
Elpi Tactic step.
Elpi Accumulate Db relations.db.
Elpi Accumulate lp:{{
  solve (goal _ _ E _ [trm F] as G) GL :-
    step E F T,
    refine T G GL.
}}.

Elpi Tactic context.
Elpi Accumulate Db relations.db.
Elpi Accumulate lp:{{
  solve (goal _ _ E _ [trm F] as G) GL :-
    step_by_context E F T, !,
    if (refine.typecheck T G GL) (1=1) (coq.ltac.fail _ "Refinement failed").
}}.


Tactic Notation "step" uconstr(te) := elpi step ltac_term:(te).
Tactic Notation "step" uconstr(te) "by" tactic(ta) :=
  elpi step ltac_term:(te); [solve [ta]|..].
Tactic Notation "calc" ":" uconstr(te) "as" ident(s) :=
  assert(s:te).
Tactic Notation "calc" ":" uconstr(te) :=
  let H := fresh "H" in
  assert(H:te).
Tactic Notation "context" uconstr(te) :=
  elpi context ltac_term:(te).

Import Nat.

Lemma test3 a b c d : (a + b) * (c + d) = (a * c + a * d + b * c + b * d).
Proof.
step (_ = (a+b)*c + (a+b)*d).
  now apply mul_add_distr_l.
context ((a+b)*c = a*c + b*c).
Show Proof.
  now apply mul_add_distr_r.
context ((a+b)*d = a*d + b*d).
  now apply mul_add_distr_r.
step (_ = a*c + b*c + a*d + b*d).
  now apply add_assoc.
context (a*c + b*c + a*d = a*c + (b*c + a*d)).
  apply eq_sym.
  now apply add_assoc.
context (b*c + _ = a*d + b*c).
  now apply add_comm.
context (a*c + (_ + _) = a*c + a*d + b*c).
  now apply add_assoc.
Qed.

Lemma rem_id a b : (a+b)^2 = a^2 + b^2 + 2*(a*b).
Proof.
step (_ = (a+b)*(a+b)).
  now apply pow_2_r.
step (_ = (a+b)*a + (a+b)*b).
  now apply mul_add_distr_l.
context ((a+b)*a = a*a + b*a).
  now apply mul_add_distr_r.
context ((a + b)*b = a*b + b*b).
  now apply mul_add_distr_r.
step (_ = a*a + b*a + a*b + b*b).
  now apply add_assoc.
context (a*a = a^2).
  apply eq_sym.
  now apply pow_2_r.
context (b*a = a*b).
  now apply mul_comm.
context (_ + a*b + a*b = a^2 + (a*b + a*b)).
  apply eq_sym.
  now apply add_assoc.
context (a*b + a*b = 2*(a*b)).
  now apply f_equal2 with (f:=plus); trivial.
context (b*b = b^2).
  apply eq_sym.
  now apply pow_2_r.
step (_ = a^2 + (2*(a*b) + b^2)).
  apply eq_sym.
  now apply add_assoc.
context (2*_ + _ = b^2 + 2*(a*b)).
  now apply add_comm.
step (_ = a^2 + b^2 + 2*(a*b)).
  now apply add_assoc.
Qed.


Lemma test4 a b c : 2 * (a * b + b * c + c * a) <= (a + b + c) ^2.
Proof.
step (_ = 2*(a*b) + 2*(b*c) + 2*(c*a)).
  context (_ = 2*(a*b + b*c) + 2*(c*a)).
    now apply mul_add_distr_l.
  apply f_equal2 with (f:=plus).
  2:trivial.
  now apply mul_add_distr_l.
step  (_ <= a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(c*a)).
  step  (2*(a*b) + 2*(b*c) + 2*(c*a) <= 2*(a*b) + 2*(b*c) + 2*(c*a) + (a^2 + b^2 + c^2)).
    now apply le_add_r.
  context (_ = a^2 + b^2 + c^2 + (2*(a*b) + 2*(b*c) + 2*(c*a))).
    now apply add_comm.
  context (2*(a*b) + 2*(b*c) + 2*(c*a) = 2*(a*b) + (2*(b*c) + 2*(c*a))).
    apply eq_sym.
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + (2*(b*c) + 2*(c*a))).
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(c*a)).
    now apply add_assoc.
step (_ = (a + b + c)^2).
  apply eq_sym.
  step ((a+b+c)^2 = (a+b)^2 + c^2 + 2*((a+b)*c)).
    now apply rem_id.
  context ((a+b)^2 = a^2 + b^2 + 2*(a*b)).
    now apply rem_id.
  context ((a+b)*c = a*c + b*c).
    now apply mul_add_distr_r.
  context (2*(a*c + b*c) = 2*(a*c) + 2*(b*c)).
    now apply mul_add_distr_l.
  step (_ = a^2 + b^2 + 2*(a*b) + c^2 + 2*(a*c) + 2*(b*c)).
    now apply add_assoc.
  context (a^2 + b^2 + 2*(a*b) + c^2 = a^2 + b^2 + (2*(a*b) + c^2)).
    apply eq_sym.
    now apply add_assoc.
  context (2*(a*b) + c^2 = c^2 + 2*(a*b)).
    now apply add_comm.
  context (_ + (_ + _) = a^2 + b^2 + c^2 + 2*(a*b)).
    now apply add_assoc.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + (2*(a*c) + 2*(b*c))).
    apply eq_sym.
    now apply add_assoc.
  context (2*(a*c) + 2*(b*c) = 2*(b*c) + 2*(a*c)).
    now apply add_comm.
  step (_ = a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(a*c)).
    now apply add_assoc.
  context (a*c = c*a).
    now apply mul_comm.
Qed.
