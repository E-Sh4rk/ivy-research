module Helper

    // Permutations

    let rec insertions x = function
        | []             -> [[x]]
        | (y :: ys) as l -> (x::l)::(List.map (fun x -> y::x) (insertions x ys))

    let rec permutations = function
        | []      -> seq [ [] ]
        | x :: xs -> Seq.concat (Seq.map (insertions x) (permutations xs))

    let all_permutations n =
        permutations (List.init n (fun i -> i))

    let permutation_to_fun lst =
        fun i -> List.item i lst

    let inv_permutation lst =
        List.init (List.length lst) (fun i -> List.findIndex (fun j -> j = i) lst)

    // Seq

    exception SeqEmpty
    let seq_min cmp seq =
        if Seq.isEmpty seq then raise SeqEmpty
        else Seq.fold (fun acc e -> if cmp e acc then e else acc) (Seq.head seq) (Seq.tail seq)

    /// <summary>
    /// Returns a sequence containing all possible combinations of choices.
    /// </summary>
    /// <param name="lst">A list of choices to take one after another. Each element is a sequence containing all possibilities for the current choice.</param>
    let rec all_choices_combination lst =
        match lst with
        | [] -> Seq.singleton []
        | h::lst ->
            let res = all_choices_combination lst
            let res = Seq.map (fun lst -> Seq.map (fun v -> v::lst) h) res
            Seq.concat res

     // List

    let list_set i e lst =
        List.mapi (fun i' e' -> if i = i' then e else e') lst

    let unzip4 lst =
        let rec aux lst (acc1,acc2,acc3,acc4) =
            match lst with
            | [] -> (List.rev acc1,List.rev acc2,List.rev acc3,List.rev acc4)
            | (h1,h2,h3,h4)::lst -> aux lst (h1::acc1,h2::acc2,h3::acc3,h4::acc4)
        aux lst ([],[],[],[])

    let lst_to_couple lst =
        (List.head lst, List.head (List.tail lst))

    let separate_hd lst =
        (List.head lst, List.tail lst)

    let separate_last lst =
        let (last, lst) = separate_hd (List.rev lst)
        (List.rev lst, last)

    let rec option_lst_to_lst olst =
        match olst with
        | [] -> []
        | None::olst -> option_lst_to_lst olst
        | (Some h)::olst -> h::(option_lst_to_lst olst)

    let foralli f lst =
        let rec aux i lst =
            match lst with
            | [] -> true
            | h::lst ->
                if f i h
                then aux (i+1) lst
                else false
        aux 0 lst

    let existsi f lst =
        not (foralli (fun x y -> not (f x y)) lst)

    // Misc

    let identity a = a

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    // Map

    let merge_maps map1 map2 =
        Map.fold (fun acc k v -> Map.add k v acc) map1 map2

    // Mutable Dictionnary

    type System.Collections.Generic.Dictionary<'K, 'V> with
        member x.TryFind(key) =
            match x.TryGetValue(key) with
            | true, v -> Some v
            | _ -> None

