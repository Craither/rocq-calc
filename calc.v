From Stdlib Require Import Arith.
From Stdlib Require Import List.
From elpi Require Import elpi.
Require Import ssrmatching.

Elpi Tactic say.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [trm F]) _ :-
    coq.say F.
}}.

Tactic Notation (at level 0) "elprint" uconstr(te) :=
  elpi say ltac_term:(te).

Check eq_trans.

Lemma f_test:
  (fun i:nat => i-i) = (fun i:nat => 0).
Proof.
  elprint (fun i:nat => i).
Abort.

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

Lemma easy_map_equal:
  forall [A B:Type] [f g:A->B] [l:list A],
    (forall x, f x = g x) -> map f l = map g l.
Proof.
  intros A B f g.
  induction l.
  simpl.
  trivial.
  intro H1.
  simpl.
  f_equal.
  apply H1.
  apply IHl.
  assumption.
Qed.

Elpi Db relations.db lp:{{
  pred trans o:term, o:term, i:term, o:term.
  pred incl o:term, o:term, o:term.
  pred step i:term, i:term, o:term.

  %If we have a direct inclusion between the last goal and the last subgoal,
  %we don't create a new goal
  step E F _ :-
    coq.unify-leq E F ok.
  
  step E F {{lp:IF _}} :-
    incl F E IF.

  %Directly apply one transitivity rule
  step E F {{lp:TF _ _}} :-
    trans F _ E TF.

  step E F {{lp:TF (lp:IF _) _}} :-
    incl F I IF,
    trans I _ E TF.

  step _ _ _ :-
    coq.ltac.fail _ "No applicable rule".


  pred step_by_context i:term, i:argument, i:argument, o:term.
  step_by_context E Y1 Y2 P' :-
    E = app L,
    std.rev L [X2,X1|_],
    step_by_context_aux X1 V Y1 Y2 P J,
    if (J = 0)(
      coq.ltac.fail _ "Pattern not found"
    ) (
      if (X2 = V) (P' = P) (
        if (trans {{lp:X1 = lp:V}} _ E TF) (
          (P' = {{lp:TF lp:P _}})
        ) (
          incl {{lp:X1 = lp:V}} I IF,
          trans I _ E TF,
          P' = {{lp:TF (lp:IF lp:P) _}}
        )
      ) 
    ).

  pred step_by_context_aux i:term, o:term, i:argument, i:argument, o:term, o:int.
  step_by_context_aux (app [F1]) (app [F2]) Y1 Y2 P I:-
    step_by_context_aux F1 F2 Y1 Y2 P I.
  
  step_by_context_aux X1 X2 (open-trm 0 Y1) (open-trm 0 Y2) P 1 :-
    coq.unify-leq X1 Y1 ok,
    coq.unify-leq X2 Y2 ok,
    TY = {{ lp:Y1 = lp:Y2 }},
    coq.typecheck-ty TY _ ok,
    coq.typecheck P TY ok.

  step_by_context_aux (app [global Map,A,C,fun N A F1,L] as X1) (app [global Map,A,C,fun N A F2,L]) Y1 Y2 P' I:-
    coq.locate "map" Map,
    coq.string->name "H" H,
    @pi-decl N A x\ (
      @pi-decl H {{In lp:x lp:L}} h\
      instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
      step_by_context_aux (F1 x) (F2 x) (Y1' x)  (Y2' x) (P x h) I
    ),
    transform_proof I X1 {{map_equal lp:{{fun N A x\ (fun H {{In lp:x lp:L}} h\ P x h)}}}} P'.

  step_by_context_aux (app [F1|L1] as X1) (app [F2|L2']) Y1 Y2 P' I :-
    app_rewrite F1 {std.rev L1} F2 L2 Y1 Y2 P I,
    std.rev L2 L2',
    transform_proof I X1 P P'.

  %step_by_context_aux (app [fun N T F1,X1|L1]) (app [fun N T F2,X2|L2]) Y1 Y2 P :-
  %  step_by_context_aux (app [F1 X1|L1]) (app [F2 X2|L2]) Y1 Y2 P.

  step_by_context_aux X X _ _ {{ refl_equal lp:X }} 0 :- name X.
  step_by_context_aux (global _ as C) C _ _ {{ @refl_equal Type lp:C }} 0 :- coq.typecheck-ty C _ ok.
  step_by_context_aux (global _ as C) C _ _ {{ refl_equal lp:C }} 0.

  pred app_rewrite i:term, i:list term, o:term, o:list term, i:argument, i:argument, o:term, o:int.
  app_rewrite F1 [] F2 [] Y1 Y2 PF I :-
    step_by_context_aux F1 F2 Y1 Y2 PF I.

  app_rewrite F1 [X1|L1] F2 [X2|L2] Y1 Y2 P' J:-
    step_by_context_aux X1 X2 Y1 Y2 PX IX,
    app_rewrite F1 L1 F2 L2 Y1 Y2 PF IF,
    J is IX + IF,
    transform_proof J (app [F1,X1|L1]) {{f_equal_equal lp:PF lp:PX}} P'.

  pred instantiate-replacement i:name, i:term, i:term, i:argument, i:argument, o:argument, o:argument.
  instantiate-replacement N Ty C L R L1 R1 :- std.do! [
    instantiate N Ty C L L1,
    instantiate N Ty C R R1,
  ].

  func transform_proof int,term,term -> term.
  transform_proof 0 X _ {{eq_refl lp:X}} :-!.
  transform_proof _ _ T T.

  pred instantiate i:name, i:term, i:term, i:argument, o:argument.
  instantiate _ _ _ (open-trm 0 A) (open-trm 0 A).
  instantiate N T C (open-trm I F) (open-trm J F1) :- 
    remove-binder-for N T C F F1,
    J is I - 1.
  instantiate _ _ _ X X.

  pred remove-binder-for i:name, i:term, i:term, i:term, o:term.
  remove-binder-for N _ C (fun N1 _ F) Res :- {coq.name->id N} = {coq.name->id N1},
    Res = (F C).
  remove-binder-for N T C (fun N1 T1 F) (fun N1 T1 F1) :-
    @pi-decl N1 T1 x \ remove-binder-for N T C (F x) (F1 x).
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
    step E F T, !,
    if (refine.typecheck T G GL) (1=1) (coq.ltac.fail _ "Refinement failed").
}}.

Elpi Tactic context.
Elpi Accumulate Db relations.db.
Elpi Accumulate lp:{{
  solve (goal _ _ E _ [(open-trm _ _ as Y1),(open-trm _ _ as Y2)] as G) GL :-
    step_by_context E Y1 Y2 T, !,
    if (refine T G GL) (1=1) (coq.ltac.fail _ "Refinement failed").
  solve _ _ :-
    coq.ltac.fail _ "Unable to fullfill the rewrite".
}}.

Tactic Notation "step" uconstr(te) := elpi step ltac_term:(te).
Tactic Notation "step" uconstr(te) "by" tactic(ta) :=
  elpi step ltac_term:(te); [solve[ta]..|idtac].
Tactic Notation "calc" ":" uconstr(te) "as" ident(s) :=
  assert(s:te).
Tactic Notation "calc" ":" uconstr(te) :=
  let H := fresh "H" in
  assert(H:te).
Tactic Notation (at level 0) "context" uconstr(t1) "=" uconstr(t2):=
  elpi context ltac_open_term:(t1) ltac_open_term:(t2); [cbv beta|cbv beta..].

Lemma fold_test:
  forall l : list nat,
    map (fun i => (i-i)) l = map (fun i => 0) l.
Proof.
  intro l.
  context (i-i) = (0).
  apply Nat.sub_diag.
Abort.

Import Nat.
Lemma test3 a b c d : (a + b) * (c + d) = (a * c + a * d + b * c + b * d).
Proof.
step (_ = (a+b)*c + (a+b)*d).
  now apply mul_add_distr_l.
context (_*c) = (a*c + b*c).
  now apply mul_add_distr_r.
context (_*d) = (a*d + b*d).
  now apply mul_add_distr_r.
step (_ = a*c + b*c + a*d + b*d).
  now apply add_assoc.
context (a*c + b*c + a*d) = (a*c + (b*c + a*d)).
  apply eq_sym.
  now apply add_assoc.
context (b*c + a*d) = (a*d + b*c).
  now apply add_comm.
context (_ + (_ + _) ) = ( a*c + a*d + b*c).
  now apply add_assoc.
Qed.

Lemma rem_id a b : (a+b)^2 = a^2 + b^2 + 2*(a*b).
Proof.
step (_ = (a+b)*(a+b)).
  now apply pow_2_r.
step (_ = (a+b)*a + (a+b)*b).
  now apply mul_add_distr_l.
context (_*a ) = (a*a + b*a).
  now apply mul_add_distr_r.
context (_*b ) = (a*b + b*b).
  now apply mul_add_distr_r.
step (_ = a*a + b*a + a*b + b*b).
  now apply add_assoc.
context (a*a) = (a^2).
  apply eq_sym.
  now apply pow_2_r.
context (b*a) = (a*b).
  now apply mul_comm.
context (a^2 + _ + _ ) = ( a^2 + (a*b + a*b)).
  apply eq_sym.
  now apply add_assoc.
context (a*b + a*b) = ( 2*(a*b)).
  now apply f_equal2 with (f:=plus); trivial.
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
Qed.


Lemma test4 a b c : 2 * (a * b + b * c + c * a) <= (a + b + c) ^2.
Proof.
step (_ = 2*(a*b) + 2*(b*c) + 2*(c*a)).
  step (_ = 2*(a*b + b*c) + 2*(c*a)).
    now apply mul_add_distr_l.
  apply f_equal2 with (f:=plus).
  2:trivial.
  now apply mul_add_distr_l.
step  (_ <= a^2 + b^2 + c^2 + 2*(a*b) + 2*(b*c) + 2*(c*a)).
  step  (2*(a*b) + 2*(b*c) + 2*(c*a) <= 2*(a*b) + 2*(b*c) + 2*(c*a) + (a^2 + b^2 + c^2)).
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
Qed.
