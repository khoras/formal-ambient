Require Import List.
Require Import ZArith.
Open Scope Z_scope.

(* K ::= cap[P] P \in CN \union AN \union {*} \un*)
Inductive CapType := Cap : list Z -> CapType.

(* m ::=  mob[P C] avec P,C \in CN \union AN \union {*} *)
Inductive MobType := Mob : (list Z * list Z) -> MobType.

(* A ::=  amb[m] *)
Inductive AmbType := Amb : MobType -> AmbType.

Inductive Capability :=
| Path : Capability -> Capability -> Capability
| In   : nat -> Capability
| Out  : nat -> Capability
| Open : nat -> Capability
.

Inductive Process :=
| Composition : Process -> Process -> Process
| Restriction : nat -> AmbType -> Process
| Replication : Process -> Process
| Action      : Capability -> Process -> Process
| Inactivity  : Process
| Ambient     : nat -> Process -> Process
.

Definition parents(m : MobType): list Z :=
match m with
| Mob (parents, _) => parents
end.

Definition childs(m : MobType): list Z :=
match m with
| Mob (_, childs) => childs
end.

Definition mob(a : AmbType): MobType :=
match a with
| Amb m => m
end.

Inductive 𝛤 :=
| Empty: 𝛤
| Cons: (Z * AmbType) -> 𝛤 -> 𝛤
.

Inductive ConcreteContexts :=
| Single : 𝛤 -> ConcreteContexts
| Multiple : 𝛤 -> ConcreteContexts -> ConcreteContexts
.

Fixpoint Inbool (a: Z) (l:list Z) : bool :=
    match l with
      | nil => false
      | b :: m => if b =? a then true else Inbool a m
end.


Fixpoint ContextUpdate (𝛾: 𝛤) ( amb: (Z * AmbType)): 𝛤 :=
match 𝛾 with
| Empty => 𝛾
| Cons (m, (Amb M0)) 𝛾 => 
      match amb with
      | (n, (Amb N)) => 
            let parentsM0 := parents M0 in
              let parentsM1 := if Inbool m (childs N) then n :: parentsM0 else parentsM0 in
            let childsM0 := childs M0 in
               let childsM1 := if Inbool m (parents N) then n :: childsM0 else childsM0 in
            Cons (m, Amb (Mob (parentsM1, childsM1))) (ContextUpdate 𝛾 amb)
      end
end.





