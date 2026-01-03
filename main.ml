let n = 9 (* hardcode pour des raisons de performance *)

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

let plus_court_chemin g depart arrivee =
	let inf = n*n+1 in

	let dist = Array.make_matrix n n inf in

	let est_arrivee s =
		List.exists (fun s' -> s = s') arrivee
	in

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
let cout j (c1: case) (c2: case) =
        let j' = joueur_oppose j in
        if c1=j' || c2=j' then 2
        else if c1=j && c2=j then 0
        else 1

(* Q3 *)
let liste_voisins (conf:configuration) j ((x,y):sommet) : (sommet*int) list =
	[(x,y-1); (x,y+1); (x-1,y); (x-1,y+1); (x+1,y-1); (x+1,y)]
	|> List.filter (dans_plateau)
	|> List.map begin
                let plateau = conf.plateau in
                let couleur = plateau.(x).(y) in (* couleur de la case (x,y) *)
                (fun (x,y) -> (
                        (x,y),
                        cout j plateau.(x).(y) couleur
                        )
                )
        end
	|> List.filter (fun (_,cout) -> cout <> 2)

(* Q4 *)
let construire_graphe config joueur =
	{
		n = n ;
		voisins = liste_voisins config joueur
	}



(* renvoie la longueur du plus court chemin entre les rives *)
let victoire_aux =
        (* precalcule pour des raisons de performance *)
        let rive1B = List.init n (fun x -> (x,0)) in
        let rive1R = List.init n (fun x -> (0,x)) in

        let rive2B = List.init n (fun x -> (x,n-1)) in
        let rive2R = List.init n (fun x -> (n-1,x)) in

        fun j ->
        let rive1,rive2,j' =
                if j=B
                then rive1B,rive2B,R
                else rive1R,rive2R,B
        in

        fun config -> 
	let rive1 = List.filter (fun (x,y) -> config.plateau.(x).(y) <> j') rive1 in
	let rive2 = List.filter (fun (x,y) -> config.plateau.(x).(y) <> j') rive2 in
	let graphe = construire_graphe config j in
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
	if victoire_R config || victoire_B config then [] else

	let j = config.joueur in
	cases
        |> List.filter (fun (x,y) -> config.plateau.(x).(y) = V)
	|> List.map (fun (x,y) -> 
		let config = {
			joueur = joueur_oppose j;
			plateau = copie config.plateau
		} in
		config.plateau.(x).(y) <- j;
		(config, (x,y))
	)

(* Q7 *)
let heuristique config = 
	let n = Array.length config.plateau in

        let l' = victoire_aux R config in
	if l' = 0 then - n*n else

	let l = victoire_aux B config in
        if l = 0 then n*n else

        l*l - l'*l'

(* Q6 *)

(* prend en entree un coup et lui associe un interet: 0 si le coup est interessant, un entier strictement negatif sinon *)
(* TODO: prebake avec la config en entree et def la liste des coups interessants *)
let interet (config: configuration) =
        let plateau = config.plateau in

        fun (c: coup) ->
        if c = (n/2,n/2) then 0 else (* prendre le centre *)

        (* on regarde si la distance minimale a une case deja remplie est inferieure ou egale a 2*)
        let (x,y) = c in
        
        (* liste des cases à 2 d'ecart *)
        [(1, 1); (2, 0); (2, -1); (2, -2); (1, 0); (1, -1); (1, -2); (0, 2); 
         (0, 1); (0, -1); (0, -2); (-1, 2); (-1, 1); (-1, 0); (-1, -1); (-2, 2);
         (-2, 1); (-2, 0)] (* TODO: optimiser l'ordre *)
	|> List.exists (fun (dx,dy) -> let x, y = x+dx, y + dy in dans_plateau (x,y) && plateau.(x).(y) <> V)
        |> function | true -> 0 | false -> -2

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
                        let res = construire_arbre config (h-1 + interet config coup) (Some coup) in
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
let choisir_coup config = minmax config 1

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

	if victoire_R config then
		Printf.printf "Vous (R) avez gagné !\n"
	else if victoire_B config then
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

        let n = 11 in  (* taille du plateau *)
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
        let p = Array.make_matrix 9 9 V in 
        {
                plateau = p;
                joueur = R;
        }
