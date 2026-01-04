let n = 11 (* hardcode pour des raisons de performance *)

let () = if n<4 then failwith "[ERREUR] Il faut n >= 4"

let infinity = 9999999


(* TYPES ---------------------------------------------------------------------------------------------------------------------------------------------- *)
type case = V | B | R

type configuration = {
        plateau : case array array; 
        joueur : case;
}

type coup = int * int

type sommet = int * int

type graphe = {
        n : int;
        voisins : sommet -> (sommet * int) list;
        (* il y a aussi les pseudo-sommets (n,0) et (n,1) pour les rives B, idem (n,2) et (n,3) pour R *)
}

type arbre_config = {
        config : configuration;
        coup : coup option;          (* None pour la racine *)
        enfants : arbre_config list;
        valeur: int
}

(* PETITES FONCTIONS ---------------------------------------------------------------------------------------------------------------------------------- *)

let joueur_oppose = function
        | B -> R
        | R -> B
        | V -> failwith "[ERREUR] Joueur vide"

let print_config config =
        let case_to_str = function
                | V -> "."
                | B -> "B"
                | R -> "r"
        in

        Printf.printf "     ";
        for i = 0 to n - 1 do
                Printf.printf "%d " i;
        done;
        print_newline ();

        for i = 0 to n - 1 do
                Printf.printf "%*s" (3 + i) "";  
                Printf.printf "%d " i;
                if i < 10 then print_string " ";

                for j = 0 to n - 1 do
                        Printf.printf "%s " (case_to_str config.plateau.(i).(j));
                done;

                print_newline ();
        done;

        Printf.printf "Au tour de : %s\n"
        (match config.joueur with B -> "Bleu" | R -> "Rouge" | _ -> "?");
        print_string "\n"

(* copie d'une matrice *)
let copie t = 
	let t2 = Array.make_matrix n n V in
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			t2.(i).(j) <- t.(i).(j);
		done;
	done;
	t2

let transpose t = 
	let t2 = Array.make_matrix n n V in
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			t2.(i).(j) <- t.(j).(i);
		done;
	done;
	t2

let plus_court_chemin g (depart: sommet list) (arrivee: sommet list) =
	let inf = n*n+1 in

	let dist = Array.make_matrix (n+1) n inf in

	let avant = ref [] in
	let arriere = ref [] in

	let push_front x =
		avant := x :: !avant
	in

	let push_back x =
		arriere := x :: !arriere
	in

	let pop () =
		match !avant with
		| x :: xs ->
				avant := xs;
				Some x
		| [] ->
				match List.rev !arriere with
				| [] -> None
				| x :: xs ->
						avant := xs;
						arriere := [];
						Some x
	in

	List.iter (fun (x, y) ->
		dist.(x).(y) <- 0;
		push_front (x, y)
	) depart;

	let rec boucle () =
		match pop () with
		| None -> ()
		| Some (x, y) ->
				let d = dist.(x).(y) in
                                List.iter (fun ((i, j), w) ->
					let nd = d + w in
					if nd < dist.(i).(j) then (
						dist.(i).(j) <- nd;
						if w = 0 then push_front (i, j)
						else push_back (i, j)
					)
				) (g.voisins (x, y));
				boucle ()
	in
	boucle ();

	let res = ref inf in
	List.iter (fun (x, y) ->
		if dist.(x).(y) < !res then
			res := dist.(x).(y)
	) arrivee;
	!res

(* SUJET ---------------------------------------------------------------------------------------------------------------------------------------------- *)

(* Q1 *)
let dans_plateau ((x,y):sommet) =
        0<=x && x < n && y>=0 && y < n
(* Q2 *)
(* le poids dans le graphe du joueur j de l'arete entre les cases c1 et c2 *)
let cout j (c: case) =
        if c=j then 0
        else if c=V then 1
        else 2

(* Q3 *)
let liste_voisins j plateau ((x,y):sommet) : (sommet*int) list =
	[(x,y-1); (x,y+1); (x-1,y); (x-1,y+1); (x+1,y-1); (x+1,y)]
	|> List.filter dans_plateau
	|> List.map begin
                (fun (x,y) -> (
                        (x,y),
                        cout j plateau.(x).(y)
                        )
                )
        end
	|> List.filter (fun (_,cout) -> cout <> 2)

(* ajoute les pseudo-sommets a la liste des voisins *)
let liste_voisins j plateau =
        if j=B
        then
                let v1 = List.init n (fun x -> ( (x,0),   cout B plateau.(x).(0)   ) ) |> List.filter (fun (_,cout) -> cout <> 2) in
                let v2 = List.init n (fun x -> ( (x,n-1), cout B plateau.(x).(n-1) ) ) |> List.filter (fun (_,cout) -> cout <> 2) in

                fun ((x,y): sommet) -> begin
                        if (x,y)=(n,0) then v1
                        else if (x,y)=(n,1) then v2
                        else
                        (
                                let c = plateau.(x).(y) in
                                if c = R then      []
                                else if y=0 then   [(n,0), 0]
                                else if y=n-1 then [(n,1), 0]
                                else               []
                        ) @ liste_voisins j plateau (x,y)
                end
        else
                let v1 = List.init n (fun x -> ( (0,x),   cout R plateau.(0).(x)   ) ) |> List.filter (fun (_,cout) -> cout <> 2) in
                let v2 = List.init n (fun x -> ( (n-1,x), cout R plateau.(n-1).(x) ) ) |> List.filter (fun (_,cout) -> cout <> 2) in

                fun ((x,y): sommet) -> begin
                        if (x,y)=(n,2) then v1
                        else if (x,y)=(n,3) then v2
                        else
                        (
                                let c = plateau.(x).(y) in
                                if c = B then      []
                                else if x=0 then   [(n,2), 0]
                                else if x=n-1 then [(n,3), 0]
                                else               []
                        ) @ liste_voisins j plateau (x,y)
                end

(* Q4 *)
let construire_graphe config joueur =
	{
		n = n ;
		voisins = liste_voisins joueur config
	}

(* renvoie la longueur du plus court chemin entre les rives *)
let victoire_aux j =
        let rive1,rive2,j' =
                if j=B
                then [(n,0)],[(n,1)],R
                else [(n,2)],[(n,3)],B
        in

        fun plateau -> 
	let graphe = construire_graphe plateau j in
	plus_court_chemin graphe rive1 rive2

let victoire_aux_B = victoire_aux B
let victoire_aux_R = victoire_aux R

let victoire_B config = victoire_aux_B config = 0
let victoire_R config = victoire_aux_R config = 0

(* Q5 *)
let coups_possibles  =
        (* precalcule pour des raisons de performance *)
        let cases = List.init n (fun x -> List.init n (fun y -> (x,y))) |> List.concat in

        fun config -> 
	if victoire_R config.plateau || victoire_B config.plateau then [] else

	let j = config.joueur in
	cases
        |> List.filter (fun (x,y) -> config.plateau.(x).(y) = V)
	|> List.map (fun (x,y) -> 
		let config = {
			joueur = joueur_oppose j;
			plateau = copie config.plateau (* ne pas recopier cette merde *)
		} in
		config.plateau.(x).(y) <- j;
		(config, (x,y))
	)

(* Q7 *)
let heuristique config = 
        let l' = victoire_aux R config.plateau in
	if l' = 0 then - 2*n*n else

	let l = victoire_aux B config.plateau in
        if l = 0 then 2*n*n else

        l'*l' - l*l

(* Q6 *)

(* prend en entree un coup et lui associe un interet: 0 si le coup est interessant, un entier strictement negatif sinon *)
(* TODO: prebake avec la config en entree et def la liste des coups interessants *)
(* TODO: test avec et sans pour voir si ca ameliore les perfs *)
let interet (config: configuration) =
        fun c -> 0
        (*
        let plateau = config.plateau in

        fun (c: coup) ->
        if c = (n/2,n/2) then 0 else (* prendre le centre *)

        (* on regarde si la distance minimale a une case deja remplie est inferieure ou egale a 2*)
        let (x,y) = c in
        
        (* liste des cases magiques (1 d'ecart / connexion) *)
        [(1, 1); (2, -1); (1, 0); (1, -1); (1, -2); (0, 1); (0, -1); (-1, 2); (-1, 1); (-1, 0); (-1, -1); (-2, 1)] (* TODO: optimiser l'ordre *)
	|> List.exists (fun (dx,dy) -> let x, y = x+dx, y + dy in dans_plateau (x,y) && plateau.(x).(y) <> V)
        |> function | true -> 0 | false -> -2
        *)

(* TODO: elagage alpha beta *)
let rec construire_arbre config h coup =
        if h <= 0 then {config=config; coup=coup; enfants=[]; valeur = heuristique config }
	else

        let valeur,comp =
                if config.joueur = B
                then ref (-infinity), (>)
                else ref (+infinity), (<)
        in

	let enfants = coups_possibles config in


	let enfants = List.map
		(fun (config, coup) -> 
                        let i = interet config coup in
                        let res = construire_arbre config (h-1+i) (Some coup) in
                        (* diminue la valeur des coups ininteressants (3 = facteur arbitraire ) *)
                        let res = {config=res.config;coup=res.coup;enfants=res.enfants; valeur = res.valeur + 100 * i } in
                        let () = if comp res.valeur !valeur then valeur := res.valeur in
                        res

		)
		enfants in
	
        {config=config; coup=coup; enfants=enfants; valeur=(!valeur)}

(* Q9 *)
let rec trouver_coup arbre =
        let enfants = arbre.enfants |> List.map
                (fun arbre -> let {coup;valeur}=arbre in match coup with | None -> failwith "[ERREUR] aaaa pas de coup" | Some coup -> (coup, valeur))
        in
        let c,_ = List.fold_left
                (fun (c,v) (c',v') -> if v>=v' then (c,v) else (c',v'))
                ( (-1,-1), -9999999)
                enfants
        in
        c

(* Q10 *)
let minmax (config: configuration) (h: int) =
        trouver_coup (construire_arbre config h None)

(* Q99 *)
let choisir_coup config = minmax config 2

(* PARTIE --------------------------------------------------------------------------------------------------------------------------------------------- *)

(* demande un coup au joueur sur l'entree standard *)
let rec saisie_coup config =
	Printf.printf "Entrez votre coup (ligne colonne) : ";
	let line = read_line () in
	try
		let i, j =
			Scanf.sscanf line "%d %d" (fun x y -> (x, y))
		in
		let n = Array.length config.plateau in
		if i < 0 || i >= n || j < 0 || j >= n then
			(Printf.printf "Coordonnées hors plateau !\n"; saisie_coup config)
		else if config.plateau.(i).(j) <> V then
			(Printf.printf "Case déjà occupée !\n"; saisie_coup config)
		else
			(i, j)
	with _ ->
		Printf.printf "Format invalide !\n";
		saisie_coup config

let jouer_coup config joueur (i,j) =
	let nouveau_plateau = copie config.plateau in
	nouveau_plateau.(i).(j) <- joueur;
	{ plateau = nouveau_plateau; joueur = joueur_oppose joueur }

let rec jeu config =
	print_config config;

	if victoire_R config.plateau then
		Printf.printf "Vous (R) avez gagné !\n"
	else if victoire_B config.plateau then
		Printf.printf "L'IA (B) a gagné !\n"
	else if config.joueur = R then begin
		(* Tour humain *)
		let coup = saisie_coup config in
		let config = jouer_coup config R coup in
		jeu config
	end else begin
		(* Tour IA *)
		Printf.printf "L'IA réfléchit...\n";
		let c = choisir_coup config in
		Printf.printf "L'IA joue %d %d\n" (fst c) (snd c);
		let config = jouer_coup config B c in
		jeu config
	end

let () =
        if input_line stdin = "" then () else begin

        let plateau_initial = Array.make_matrix n n V in
        let config_initial = { plateau = plateau_initial; joueur = R } in
        print_string "Debut de la partie\n\n";
        jeu config_initial

        end

(* EXEMPLES ------------------------------------------------------------------------------------------------------------------------------------------- *)
let ec1 =
        let n = 9 in
        let p = Array.make_matrix n n V in

        p.(0).(2) <- B;
        p.(1).(2) <- R;
        p.(0).(3) <- R;
        p.(2).(3) <- B;
        p.(2).(2) <- R;
        p.(3).(2) <- R;
        p.(3).(3) <- R;
        p.(4).(2) <- R;
        p.(5).(2) <- R;
        p.(5).(3) <- R;
        p.(6).(2) <- R;
        p.(7).(2) <- R;
        p.(7).(3) <- R;
        p.(8).(2) <- R;
        {
                plateau = p;
                joueur = R;
        }

let ec2 =
        let p = Array.make_matrix n n V in 
        {
                plateau = p;
                joueur = R;
        }

let ec3 =
        let n = 11 in
        let p = Array.make_matrix n n V in

        p.(0).(8) <- R;
        p.(1).(8) <- R;
        p.(1).(9) <- R;
        p.(2).(7) <- R;
        p.(3).(6) <- R;
        p.(4).(6) <- R;
        p.(5).(6) <- R;
        p.(6).(6) <- R;
        p.(7).(6) <- R;
        p.(8).(6) <- R;
        p.(10).(4) <- R;
        {
                plateau = p;
                joueur = B;
        }
