(* Funzione ausiliaria per leggere il valore di una variabile.
   1. 'topenv st x' cerca l'identificatore x nell'ambiente in cima allo stack (scope corrente).
   2. Se è una variabile (IVar l), usa 'getmem' per leggere il valore intero alla locazione l. *)
let apply st x = match topenv st x with
    IVar l -> getmem st l
  | _ -> failwith "apply error"

(* Funzione di parsing: prende una stringa, crea un lexer buffer e invoca il parser
   per produrre l'Albero di Sintassi Astratta (AST) del programma. *)
let parse (s : string) : prog =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

(******************************************************************************)
(* Small-step semantics of expressions                   *)
(******************************************************************************)

(* Eccezioni per gestire errori a runtime *)
exception TypeError of string
exception UnboundVar of string
exception PredOfZero
exception NoRuleApplies

(* Definizioni di base per ambienti e memoria vuoti/iniziali *)
let botenv = fun x -> failwith ("variable " ^ x ^ " unbound")
let botmem = fun l -> failwith ("location " ^ string_of_int l ^ " undefined")
    
(* Funzione per aggiornare un ambiente o una memoria (binding).
   Restituisce una nuova funzione che mappa x a v, e lascia invariati gli altri input. *)
let bind f x v = fun y -> if y = x then v else f y

(* Predicato che determina se un'espressione è un "valore" (forma normale irriducibile).
   True, False e le costanti numeriche sono valori. *)
let is_val = function
    True -> true
  | False -> true
  | Const _ -> true
  | _ -> false

(* SEMANTICA SMALL-STEP DELLE ESPRESSIONI (trace1_expr)
   Riduce un'espressione di un passo. Restituisce la nuova espressione e il nuovo stato. *)
let rec trace1_expr st = function
  (* Dereferenziazione variabile: sostituisce la var col suo valore intero *)
  | Var x -> (Const(apply st x), st)
  
  (* Regole per la negazione logica (Not) *)
  | Not(True) -> (False,st)
  | Not(False) -> (True,st)
  | Not(e) -> let (e',st') = trace1_expr st e in (Not(e'),st') (* Riduzione congruente *)
  
  (* Regole per l'AND logico (short-circuit evaluation) *)
  | And(True,e) -> (e,st)
  | And(False,_) -> (False,st)
  | And(e1,e2) -> let (e1',st') = trace1_expr st e1 in (And(e1',e2),st')
  
  (* Regole per l'OR logico *)
  | Or(True,_) -> (True,st)
  | Or(False,e) -> (e,st)
  | Or(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Or(e1',e2),st')
  
  (* Regole per l'Addizione *)
  | Add(Const(n1),Const(n2)) -> (Const(n1+n2),st) (* Caso base: somma due costanti *)
  | Add(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Add(Const(n1),e2'),st') (* Riduci operando destro *)
  | Add(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Add(e1',e2),st') (* Riduci operando sinistro *)
  
  (* Regole per Sottrazione e Moltiplicazione (analoghe all'Addizione) *)
  | Sub(Const(n1),Const(n2)) -> (Const(n1-n2),st)
  | Sub(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Sub(Const(n1),e2'),st')
  | Sub(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Sub(e1',e2),st')
  | Mul(Const(n1),Const(n2)) -> (Const(n1*n2),st)
  | Mul(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Mul(Const(n1),e2'),st')
  | Mul(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Mul(e1',e2),st')
  
  (* Regole per Uguaglianza (Eq) e Minore o Uguale (Leq) *)
  | Eq(Const(n1),Const(n2)) -> if n1=n2 then (True,st) else (False,st)
  | Eq(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Eq(Const(n1),e2'),st')
  | Eq(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Eq(e1',e2),st')
  | Leq(Const(n1),Const(n2)) -> if n1<=n2 then (True,st) else (False,st)
  | Leq(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Leq(Const(n1),e2'),st')
  | Leq(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Leq(e1',e2),st')

  (* --- GESTIONE CHIAMATE DI FUNZIONE --- *)
  
  (* Caso Call(f, v): L'argomento è già valutato (è una costante n).
     Dobbiamo preparare l'ambiente per l'esecuzione della funzione. *)
  | Call(f,Const(n)) -> (match (topenv st) f with
        (* Cerchiamo la definizione di f nell'ambiente corrente *)
        IFun(x,c,er) ->
        let l = getloc st in                    (* Ottieni la prima locazione libera in memoria *)
        let env' = bind (topenv st) x (IVar l) in (* Crea nuovo ambiente bindando il parametro formale x alla loc l *)
        let mem' = bind (getmem st) l n in      (* Scrivi il valore n (parametro attuale) nella memoria alla loc l *)
        (* Costruisci il nuovo stato:
           - Push di env' in cima allo stack degli ambienti (env' :: getenv st)
           - Memoria aggiornata
           - Incremento contatore locazioni (l+1) *)
        let st' = (env'::(getenv st), mem', l+1) in
        (* L'espressione diventa CallExec: sta eseguendo il corpo c *)
        (CallExec(c,er),st')
      | _ -> raise (TypeError "Call of a non-function"))
  
  (* Caso Call(f, e): L'argomento non è ancora un valore, va ridotto prima *)
  | Call(f,e) -> let (e',st') = trace1_expr st e in (Call(f,e'),st')

  (* Caso CallExec(c, e): Stiamo eseguendo il corpo 'c' della funzione *)
  | CallExec(c,e) -> (match trace1_cmd (Cmd(c,st)) with
      St st' -> (CallRet(e),st')       (* Se il comando è finito (diventa St), passiamo a valutare il ritorno (CallRet) *)
    | Cmd(c',st') -> (CallExec(c',e),st')) (* Se il comando non è finito, continua a eseguirlo mantenendo CallExec *)

  (* Caso CallRet(v): Il ritorno è già valutato. Bisogna uscire dalla funzione. *)
  | CallRet(Const(n)) -> 
      (* 'popenv st' rimuove l'ambiente locale dalla cima dello stack (POP) *)
      let st' = (popenv st, getmem st, getloc st) in 
      (Const(n),st') (* L'intera chiamata di funzione è ora ridotta al valore n *)
  
  (* Caso CallRet(e): L'espressione di ritorno va ancora ridotta *)
  | CallRet(e) -> let (e',st') = trace1_expr st e in (CallRet(e'),st')

  (* Nessuna regola applicabile *)
  | _ -> raise NoRuleApplies

(* SEMANTICA SMALL-STEP DEI COMANDI (trace1_cmd)
   Riduce una configurazione (Comando, Stato) in una nuova configurazione.
   Puo restituire Cmd(c', st') se c'è ancora da fare, o St(st') se il comando è terminato. *)
and trace1_cmd = function
    St _ -> raise NoRuleApplies (* Non si può ridurre uno stato finale *)
  | Cmd(c,st) -> match c with
      (* Skip: comando nullo, termina l'esecuzione ritornando solo lo stato *)
      Skip -> St st
    
    (* Assegnamento Assign(x, v): l'espressione è già una costante *)
    | Assign(x,Const(n)) -> (match topenv st x with
        (* Cerca la locazione l associata a x e aggiorna la memoria *)
        IVar l -> St (getenv st, bind (getmem st) l n, getloc st)
      | _ -> failwith "improve err msg")
    
    (* Assegnamento Assign(x, e): riduci l'espressione a destra *)
    | Assign(x,e) -> let (e',st') = trace1_expr st e in Cmd(Assign(x,e'),st') 
    
    (* Sequenza Seq(c1, c2): esegui un passo di c1 *)
    | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st)) with
          St st1 -> Cmd(c2,st1)           (* Se c1 è finito, resta c2 da eseguire *)
        | Cmd(c1',st1) -> Cmd(Seq(c1',c2),st1)) (* Se c1 continua, aggiorna la sequenza *)
    
    (* If-then-else *)
    | If(True,c1,_) -> Cmd(c1,st)  (* Condizione vera: esegui ramo then *)
    | If(False,_,c2) -> Cmd(c2,st) (* Condizione falsa: esegui ramo else *)
    | If(e,c1,c2) -> let (e',st') = trace1_expr st e in Cmd(If(e',c1,c2),st') (* Riduci la condizione *)
    
    (* While: srotolamento in un If *)
    | While(e,c) -> Cmd(If(e,Seq(c,While(e,c)),Skip),st)

(* SEMANTICA DELLE DICHIARAZIONI (sem_decl)
   Elabora le dichiarazioni per costruire l'ambiente e lo stato iniziale. *)
let rec sem_decl (e,l) = function
    EmptyDecl -> (e,l)
  (* IntVar: Associa x alla locazione l corrente e incrementa l *)
  | IntVar(x) ->  let e' = bind e x (IVar l) in (e',l+1)
  (* Fun: Associa f alla definizione della funzione (IFun) nell'ambiente.
     Nota: non incrementa l perché la funzione risiede nell'ambiente, non in memoria dati *)
  | Fun(f,x,c,er) -> let e' = bind e f (IFun(x,c,er)) in (e',l)
  (* Sequenza di dichiarazioni: elabora d1 poi d2 *)
  | DSeq(d1,d2) -> let (e',l') = sem_decl (e,l) d1 in sem_decl (e',l') d2


(* Loop principale di esecuzione (trace_rec)
   Esegue n passi della semantica small-step accumulando gli stati intermedi in una lista. *)
let rec trace_rec n t =
  if n<=0 then [t]
  else try
      let t' = trace1_cmd t
      in t::(trace_rec (n-1) t')
    with NoRuleApplies -> [t]


(**********************************************************************
 trace : int -> prog -> conf list

 Usage: trace n c performs n steps of the small-step semantics
 **********************************************************************)

(* Entry point della traccia.
   1. Elabora le dichiarazioni (sem_decl) partendo da env vuoto e loc 0.
   2. Avvia la traccia del comando principale c con lo stato inizializzato. *)
let trace n (Prog(d,c)) =
  let (e,l) = sem_decl (botenv,0) d
  (* Lo stato iniziale ha una lista contenente un solo ambiente [e] *)
  in trace_rec n (Cmd(c,([e],botmem,l)))