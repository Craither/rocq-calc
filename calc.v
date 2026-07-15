From Stdlib Require Import Arith.
From Stdlib Require Import List.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma f_equal_equal:
  forall [A B:Type] [f1 f2: A->B] [x1 x2:A], f1 = f2 -> x1 = x2 -> f1 x1 = f2 x2.
Proof.
  intros A B f1 f2 x1 x2 H1 H2.
  exact (eq_trans (f_equal (fun f : A -> B => f x1) H1) (f_equal f2 H2)).
  Show Proof.
Qed.
Set Printing All.
Check ( _ : _).
Check ((nat):eqType).

Elpi Command say.
Elpi Accumulate lp:{{
  main [trm F] :-
    coq.say F,
    coq.typecheck-ty {{lp:F:(eqType)}} _ ok.
}}.

Lemma fold_equal:
  forall [A B:Type] [f g:A->B->A] [l1 l2:list B] [i1 i2:A],
    l1 = l2 -> i1 = i2 -> (forall [x:A] [y:B],  In y l1 -> f x y = g x y) -> fold_left f l1 i1 = fold_left g l2 i2.
Proof.
  intros A B f g l1 l2 i1 i2 H1 H2.
  destruct H1.
  destruct H2.
  generalize i1.
  induction l1.
  simpl.
  trivial.
  intros i H.
  simpl.
  assert (H':f i a = g i a).
  apply H.
  simpl.
  apply or_introl.
  apply Corelib.Init.Logic.eq_refl.
  destruct H'.
  apply IHl1.
  intros x y.
  intro H''.
  apply H.
  simpl.
  apply or_intror.
  assumption.
Qed.

Lemma map_equal:
  forall [A B:Type] [f g:A->B] [l1 l2:list A],
    l1 = l2 -> (forall [x:A], In x l1 -> f x = g x) -> map f l1 = map g l2.
Proof.
  intros A B f g l1 l2 H H1.
  destruct H.
  induction l1.
  simpl.
  apply Corelib.Init.Logic.eq_refl.
  simpl.
  f_equal.
  apply H1.
  simpl.
  apply or_introl.
  reflexivity.
  apply IHl1.
  intros x H2.
  apply H1.
  simpl.
  apply or_intror.
  assumption.
Qed.

Check eq_bigr.

Lemma eq_bigr_no_pred:
  forall [R:Type] [idx: R] [op: R->R->R] [I:Type] [r:seq I] [F1:I->R] (F2:I->R),
    (forall i:I, F1 i = F2 i) -> 
      \big[op/idx]_(i <- r)  F1 i =
      \big[op/idx]_(i <- r)  F2 i.
Proof.
  intros R idx op I r F1 F2 H.
  apply eq_bigr.
  intros i H1.
  apply H.
Qed.

Lemma eq_big_all:
  forall [R:Type] [idx:R] [op: R->R->R] [I:eqType] [r:seq I] [P1:pred I] (P2:pred I) [F1:I->R] (F2:I->R),
  {in r, P1 =1 P2} ->
  (forall i:I, i \in r -> P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P1 i)  F1 i = \big[op/idx]_(i <- r | P2 i)  F2 i.
Proof.
  intros R idx op I r P1 P2 F1 F2 H1 H2.
  transitivity (\big[op/idx]_(i <- r | (i \in r) && P1 i)  F1 i).
  apply big_seq_cond.
  transitivity ((\big[op/idx]_(i <- r | (i \in r) && P2 i)  F2 i)).
  apply eq_big.
  intro i.
  apply Bool.eq_true_iff_eq.
  firstorder.
  apply andb_true_intro.
  apply conj.
  apply andb_prop in H.
  destruct H.
  assumption.
  apply andb_prop in H.
  destruct H.
  transitivity (P1 i).
  2:assumption.
  rewrite H1.
  reflexivity.
  apply H.
  apply andb_true_intro.
  apply conj.
  apply andb_prop in H.
  destruct H.
  assumption.
  apply andb_prop in H.
  destruct H.
  transitivity (P1 i).
  reflexivity.
  rewrite H1.
  apply H0.
  apply H.
  intros i H3.
  apply H2.
  apply andb_prop in H3.
  destruct H3.
  apply H.
  apply andb_prop in H3.
  destruct H3.
  apply H0.
  apply Logic.eq_sym.
  apply big_seq_cond.
Qed.

Goal \sum_(0<= i < 2) i = 0.
Proof.
  Search "eq" "big" (mem).
  rewrite (eq_big_seq (fun i => i + i)).
Abort.

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

  step_by_context_aux X1 Y2 (open-trm 0 Y1) (open-trm 0 Y2) _ 1 :-
    coq.typecheck X1 Ty ok,
    coq.typecheck Y2 Ty ok,
    coq.unify-leq X1 Y1 ok.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- index_iota lp:N1 lp:N2) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- index_iota lp:N1 lp:N2) lp:(F2 i) }} Y1 Y2 P' J :-
    X1 = {{ @bigop.body lp:A _ _ _ lp:{{ fun N _ _}} }},
    coq.typecheck Idx A ok,
    @pi-decl N A x\ (
      coq.string->name "H" H0,
      fresh-name H0 {{lp:N1 <= lp:x < lp:N2}} H,
      @pi-decl H {{lp:N1 <= lp:x < lp:N2}} h\ (
        instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
        step_by_context_aux (F1 x) (F2 x) (Y1' x)  (Y2' x) (Prf x h) IF
      )
    ),
    J is IF,
    transform_proof J X1 {{eq_big_nat _ _ lp:{{fun N A x\ (fun H {{lp:N1 <= lp:x < lp:N2 }} h\ Prf x h)}}}} P'.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F2 i) }} Y1 Y2 P' J :-
    X1 = {{ @bigop.body lp:A _ _ _ lp:{{ fun N _ _}} }},
    coq.typecheck Idx A ok,
    @pi-decl N A x\ (
        instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
        step_by_context_aux (F1 x) (F2 x) (Y1' x)  (Y2' x) (Prf x) IF
    ),
    J is IF,
    transform_proof J X1 {{eq_bigr_no_pred lp:{{fun N A x\ Prf x }}}} P'.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L| lp:(P1 i)) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L | lp:(P2 i)) lp:(F2 i) }} Y1 Y2 P' J :-
    X1 = {{ @bigop.body lp:A _ _ _ lp:{{ fun N _ _}} }},
    coq.typecheck Idx A ok,
    @pi-decl N A x\ (
      coq.string->name "H" H0,
      fresh-name H0 (P x) H,
      instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
      step_by_context_aux (P1 x) (P2 x) (Y1' x) (Y2' x) (PP x) IP,
      @pi-decl H (P1 x) h\ (
        step_by_context_aux (F1 x) (F2 x) (Y1' x) (Y2' x) (PF x h) IF
      )
    ),
    J is IF + IP,
    transform_proof J X1 {{eq_big lp:{{fun N A P2}} lp:{{fun N A F2}} lp:{{fun N A PP}} lp:{{fun N A x\ (fun H (P x) h\ PF x h)}}}} P'.


  step_by_context_aux (app [global Map,A,C,fun N A F1,L1] as X1) (app [global Map,A,C,fun N A F2,L2]) Y1 Y2 P' J:-
    coq.locate "map" Map,
    step_by_context_aux L1 L2 Y1 Y2 PL IL,
    @pi-decl N A x\ (
      coq.string->name "H" H0,
      fresh-name H0 {{In lp:x lp:L}} H,
      @pi-decl H {{In lp:x lp:L}} h\ (
        instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
        step_by_context_aux (F1 x) (F2 x) (Y1' x)  (Y2' x) (P x h) IF
      )
    ),
    J is IL + IF,
    transform_proof J X1 {{map_equal lp:PL lp:{{fun N A x\ (fun H {{In lp:x lp:L}} h\ P x h)}}}} P'.
  
  step_by_context_aux (app [global Fold,A,B,(fun Nx A x\ fun Ny B y\ F1 x y),L1,I1] as X1) (app [global Fold,A,B,(fun Nx A x\ fun Ny B y\ F2 x y),L2,I2]) Y1 Y2 P' J :-
    coq.locate "fold_left" Fold,
    step_by_context_aux L1 L2 Y1 Y2 PL IL,
    step_by_context_aux I1 I2 Y1 Y2 PI II,
    @pi-decl Nx A x\ (
      @pi-decl Ny B y\ (
        coq.string->name "H" H0,
        fresh-name H0 {{In lp:y lp:L1}} H,
        @pi-decl H {{In lp:y lp:L1}} h\ (
          instantiate-replacement Nx A x Y1 Y2 (Y1' x) (Y2' x),
          instantiate-replacement Ny B y (Y1' x) (Y2' x) (Y1'' x y) (Y2'' x y),
          step_by_context_aux (F1 x y) (F2 x y) (Y1'' x y) (Y2'' x y) (P x y h) IF
        )
      ) 
    ),
    J is IL + II + IF,
    transform_proof J X1 {{fold_equal lp:PL lp:PI lp:{{fun Nx A x\ (fun Ny B y\ (fun H {{In lp:y lp:L1}} h\ P x y h))}}}} P'.

  step_by_context_aux (app [F1|L1] as X1) (app [F2|L2']) Y1 Y2 P' I :-
    app_rewrite F1 {std.rev L1} F2 L2 Y1 Y2 P I,
    std.rev L2 L2',
    transform_proof I X1 P P'.

  step_by_context_aux (app [fun N T F1,X1|L1]) (app [fun N T F2,X2|L2]) Y1 Y2 P I:-
    step_by_context_aux (app [F1 X1|L1]) (app [F2 X2|L2]) Y1 Y2 P I.

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
  transform_proof 0 X _ {{Corelib.Init.Logic.eq_refl lp:X}} :-!.
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

  pred preserve_bound_variables i:term o:term.

  preserve_bound_variables I O :-
    (((pi N T F N1 T1 F1 \
      copy (fun N T F) (fun N1 T1 F1) :-!,
      copy T T1,
      fresh-name N T N1,
      (@pi-decl N1 T1 x\
        copy (F x) (F1 x))),
      (pi B B1 N T F N1 T1 F1 \
        copy (let N T B F)(let N1 T1 B1 F1) :-!,
          copy T T1,
          copy B B1,
          fresh-name N T N1,
          (@pi-decl N1 T1 x\ copy (F x) (F1 x))),
      (pi N T F N1 T1 F1 \
        copy (prod N T F) (prod N1 T1 F1) :-!,
          copy T T1,
          fresh-name N T N1,
          (@pi-decl N1 T1 x\
            copy (F x) (F1 x)))) => copy I O).

  pred fresh-name i:name, i:term, o:name.

  fresh-name N T M :-
    coq.ltac.fresh-id {coq.name->id N} T Mi,
    coq.id->name Mi M.
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
  solve (goal _ _ E0 _ [(open-trm _ _ as Y1),(open-trm _ _ as Y2)] as G) GL :-
    preserve_bound_variables E0 E,
    step_by_context E Y1 Y2 T,
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

Lemma map_test:
  forall l,
    map (fun i => map (fun j => i + j + 0) (0::nil)) l = map (fun i => i::nil) l.
Proof.
  intro l.
  context (i + j + 0) = (i + j).
  apply Nat.add_0_r.
Abort.

Lemma fold_test:
  forall l,
    fold_left (fun acc i => acc*i + 2) l 0 = fold_left (fun acc i => acc*i + 0 + 2) l 0.
Proof.
  intro l.
  context (acc*i) = (acc*i + 0).
  apply Logic.eq_sym.
  apply Nat.add_0_r.
Qed.

Lemma sum_test1:
  \sum_(0 <= i < 6) (\prod_(7<= j < 9) (i + j)) = \sum_(0 <= i < 6) (\prod_(7<= j < 9) (j + i)).
Proof.
  context (i + j) = (j + i).
  apply Nat.add_comm.
  Show Proof.
Qed.

Lemma sum_test2:
  \sum_(0 <= i < 6 | (i + 2) == 6) (i) = 3^2.
Proof.
  context i = (i + 0).
  apply Logic.eq_sym.
  apply Nat.add_0_r.
  apply Logic.eq_sym.
  apply Nat.add_0_r.
Abort.

Import Nat.
Lemma test3 a b c d : (a + b) * (c + d) = (a * c + a * d + b * c + b * d).
Proof.
step (_ = (a+b)*c + (a+b)*d).
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
Qed.

Open Scope nat_scope.

Lemma test4 a b c : ((2 * (a * b + b * c + c * a)) <= ((a + b + c) ^2))%coq_nat.
Proof.
step (_ = 2*(a*b) + 2*(b*c) + 2*(c*a)).
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