type ide = string;;
type exp =
    Eint of int
  | Ebool of bool
  | Estring of string
  | Den of ide
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  | Eq of exp * exp
  | Minus of exp
  | IsZero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * exp
  | Letrec of ide * exp *exp
  | ApplyOver of exp * exp 
  | Update of exp * exp
  | Remove of ide * exp
  | Dict of (ide * exp) list
  | Clear of exp
  | Select of exp * ide

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT =
    Int of int
  | Bool of bool
  | String of string
  | Unbound
  | FunVal of evFun
  | RecFunVal of ide * evFun
  | DictVal of (ide * evT) list 

and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	| "int" -> (match v with
		|Int(_) -> true 
		|_ -> false) 
	| "bool" -> (match v with
		|Bool(_) -> true 
		|_ -> false) 
        | "string" -> (match v with
		|String(_) -> true 
		|_ -> false) 
	|_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y) then
    ( match ( x, y) with 
        ( Int(n), Int(u) ) -> Int(n * u )
      | _ -> failwith (" Type error "))
  else failwith ( "Type error" );;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Int(n+u)
         | _-> failwith("Type error"))
  else failwith("Type error");;


let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Int(n-u)
         | _-> failwith("Type error"))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
           (Int(n),Int(u)) -> Bool(n=u)
         | _-> failwith("Type error"))
  else failwith("Type error");;

let minus x = if (typecheck "int" x) 
  then (match x with
           Int(n) -> Int(-n)
         | _-> failwith("Type error"))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
           Int(n) -> Bool(n=0)
         | _-> failwith("Type error"))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
           (Bool(b),Bool(e)) -> (Bool(b||e))
         | _-> failwith("Type error"))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
           (Bool(b),Bool(e)) -> Bool(b&&e)
         | _-> failwith("Type error"))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
           Bool(true) -> Bool(false) |
           Bool(false) -> Bool(true)
         | _-> failwith("Type error"))
  else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
        Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	Dict(lst) -> DictVal(evalList lst r) |
        Clear(lst) -> DictVal(evalList [] r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
        FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
				   let aVal = (eval eArg r) in
				   let rEnv = (bind fDecEnv g fClosure) in

				   let aEnv = (bind rEnv arg aVal) in
					eval fBody aEnv |
				_ -> failwith("non functional value"))  |
	Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> 
				let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                   			eval letBody r1 |
            		_ -> failwith("non functional def")) |
        ApplyOver ( e1 , e2 ) -> 
	      let f = eval e1 r in
	      let a = eval e2 r in 
	        (match f , a with 
	          | FunVal(_) , DictVal(t) -> DictVal( (applyover f t  ) )
	          | _ , _ -> failwith ("no functional value") ) |
       Update( e1 , e2 ) -> 
	      let f = eval e1 r in
	      let a = eval e2 r in 
	        (match f , a with 
	          | FunVal(_) , DictVal(t) -> DictVal( (update f t  ) )
	          | _ , _ -> failwith ("no functional value") ) |
        Select(rd, id) ->
		(match (eval rd r) with
		DictVal(rdPairs) -> select id rdPairs |
		_ -> failwith("wrong select value")) |
        Remove( id , e2 ) -> 
             (match (eval e2 r) with 
	          DictVal(t) -> DictVal( (remove id t  ) )
	          |  _ -> failwith ("no functional value") )

and evalList (lst : (ide * exp) list) (r : evT env) : (ide * evT) list = match lst with
	|[ ] -> [ ] 
	| (id, arg)::rest -> (id, eval arg r) :: evalList rest r 

and applyover f t = match f, t with 
  | FunVal( arg , body, r1) , (id,second)::rest -> if(typecheck "string" second) then applyover f rest else (id, eval body (bind r1 arg second))::(applyover f rest)
  |_ , []-> []
  |_,_ -> failwith ("Invalid Argument")


and select (id : ide) (lst : (ide * evT) list) : evT = match lst with
	|[ ] -> Unbound 
	| (id1,asso)::rest -> if (id=id1) then asso else (select id rest)

and update f t = match f, t with 
  | FunVal( arg , body, r1) , [] -> 
           (arg, eval body r1 )::[]
  | FunVal( arg , body, r1) , (id,second)::rest -> 
           (arg, eval body r1 )::(id,second)::rest 
  |_,_ -> failwith ("Invalid Argument")

and remove arg t = match t with 
  | (id,second)::rest -> 
          if (arg=id) then rest else (id,second)::(remove arg rest)
  | []-> []
;;

(*---------------------------------TEST GENERICI-------------------------*)

(*diichiaro i parametri da aggiungere ai dizionari*)
let matricola=Eint 123456;;
let nome=Estring "Giovanni";;

(*dichiaro i dizionari*)

let dizionario=Dict([("nome",nome);("matricola",matricola)]);;
let dizionario1=Dict([]);;
let dizionario2=Dict([("nome",Estring "Domenico")]);;

(*Ambiente*)
let env0 = emptyenv Unbound;;
let env1= bind env0 "x" (Int( 5));;

(*Test valutazione dizionari*)
eval dizionario env0;;
eval dizionario1 env0;;
eval dizionario2 env0;;

(*chiamo la funzione di selezione dell'elemento nome,matricola ed età*)
let get = Select(dizionario,"nome");;
let get1 = Select(dizionario,"matricola");;
(*la get2 restituisce unbound perchè età non è presente*)
let get2 = Select(dizionario,"anni");;

(*test operazione di selezione*)
eval get env0;;
eval get1 env0;;
eval get2 env0;;

(*dichiaro la funzione da aggiungere al dizionario*)
let updatefun = Fun("eta",Eint 22);;

(*chiamo la funzione update per aggiungere età al dizionario*)
let testupdate=Update(updatefun, dizionario);;
let testupdate1=Update(updatefun, dizionario1);;

(*Test operazione di update*)
eval testupdate env0;;
eval testupdate1 env0;;

(*chiamo la funzione per rimuovere "matricola" al dizionario*)
let testremove=Remove("matricola", dizionario);;
let testremove1=Remove("matricola", dizionario1);;

(*Test operazione di remove su dizionario*)
eval testremove env0;;
(*Test operazione di remove su dizionario1 non rimuove nulla dato che è vuoto*)
eval testremove1 env0;;

(*chiamo la funzione per cancellare il dizionario*)
let testclear=Clear(dizionario);;
let testclear1=Clear(dizionario2);;

(*Test operazione clear su dizionario*)
eval testclear env0;;
eval testclear1 env1;;

(*definizioni delle funzioni utilizzate nei dell'apply*)
let f = Fun("x",Sum(Eint 70,Den "x"));;
let f1 = Fun("x",Eq(Den "x",Eint 123456));;
let f2 = Fun("x",And(Den "x",Ebool(true)));;
let f3 = Fun("x",IsZero(Den"x"));;

(*chiamo la funzione apply*)
let testapply=ApplyOver(f,dizionario);;
let testapply1=ApplyOver(f1,dizionario);;
let testapply2=ApplyOver(f2,dizionario);;
let testapply3=ApplyOver(f3,dizionario);;

(*eseguo l'apply nell ambiente env1*)
eval testapply env1;;
(*(eval testapply2 env1) da errore di tipo *)
eval testapply1 env1;;
eval testapply3 env1;;

(*-------------TEST SINTASSI CONCRETA---------------*)

let my_dict=Dict([]);;

let my_dict=Dict([("name",Estring "Giovannni");("matricola",Eint 123456)]);;

let get = Select(my_dict,"name");;
eval get env0;;

let get1 = Select(my_dict,"matricola");;
eval get1 env0;;

let my_dict1=Update(Fun("eta",Eint 22), my_dict);;
eval my_dict1 env0;;

let my_dict2=Remove("name", my_dict1);;
eval my_dict2 env0;;

let my_dict3 = Clear(my_dict2);;
eval my_dict3 env0;;

let testapply=ApplyOver(Fun("x",Sum(Eint 1,Den "x")),my_dict2);;
eval testapply env0;;