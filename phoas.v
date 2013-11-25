
Inductive T :=
| E : Type -> T
| Arrow: T -> T -> T.
Section t. 
  Variable var: T -> Type.
  
  Inductive term: T -> Type :=
    | Var: forall t, var t -> term t
    | Abs: forall alpha beta, (var alpha -> term beta) -> term (Arrow alpha beta)
    | App: forall alpha beta, term (Arrow alpha beta) -> term alpha -> term beta.

End t. 
Definition Term t := forall var, term var t.
Set Implicit Arguments.
Fixpoint size t (e : term (fun _ => unit) t) : nat := 
match e with
| Var t v => 1
| Abs alpha beta e => 1 + size (e tt)
| App _ _ e f => 1+ size e + size f
end.

Arguments Abs {var} {alpha beta} _.
Arguments App {var} {alpha beta} _ _.
Arguments Var {var} {t} _ .
Definition K alpha beta : Term (Arrow alpha (Arrow beta alpha)) := 
  fun var => Abs (fun x => Abs    (fun y => Var  x)).
                  

Fixpoint tdenote t : Type :=
match t with
    E tau => tau
  | Arrow alpha beta => tdenote alpha -> tdenote beta
end.
 
Fixpoint denote {t} (e: term tdenote t) : tdenote t :=
match e with
| Var t v => v
| Abs alpha beta e => fun x => denote (e x)
| App _ _ e f => (denote e) (denote f)
end.


Eval compute in denote ((K (E nat) (E nat)) _). 
Eval compute in size ((K (E nat) (E nat)) _). 

 Section wf.
    Variables var1 var2 : T -> Type.

    Record varEntry := {
                        Ty : T;
                        First : var1 Ty;
                        Second : var2 Ty
                      }.
    Require Import List.
    Inductive wf : list varEntry -> forall t, term var1 t -> term var2 t -> Prop :=
    | WfVar : forall G t x x', List.In {| Ty := t; First := x; Second := x' |} G
      -> wf G (Var x) (Var x')
    | WfAbs : forall G dom ran (e1 : _ dom -> term _ ran) e1',
      (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e1 x1) (e1' x2))
      -> wf G (Abs e1) (Abs e1')

    | WfApp : forall G dom ran (e1 : term _ (Arrow dom ran)) (e2 : term _ dom) e1' e2',
      wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (App e1 e2) (App e1' e2').

  End wf.