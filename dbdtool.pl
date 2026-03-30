% =====================================================================
% TOOLKIT: DATABASE DESIGN (dbdtool.pl) 
% Lecturer: Nguyen Van Dieu
% =====================================================================
:- module(dbdtool, [
    checkFD/3,
    xplus/4, 
    equivalent/2,  
    projectFD/3,                 
    mincover/2,      
    candkey/3, 
    is2NF/2,
    is3NF/2,
    isBCNF/2,
    normalF/3,
    isLossChase/3,
    decomposition/2         
]).

:- op(500, xfy, ==>).
:- style_check(-singleton). 

% ---------------------------------------------------------------------
% 1. Tien ich 
% ---------------------------------------------------------------------
subset([], _).
subset([H|T], List) :- member(H, List), subset(T, List).

% Sinh tập con (subset_gen/2)
subset_gen([], []).
subset_gen([H|T], [H|Sub]) :- subset_gen(T, Sub).
subset_gen([_|T], Sub) :- subset_gen(T, Sub).

% Powerset dung cho discoverFDs
powerset([], [[]]).
powerset([H|T], P) :-
    powerset(T, P1),
    maplist({H}/[X, [H|X]]>>true, P1, P2),
    append(P1, P2, P).

% Lay gia tri theo ten cot
get_vals_by_name([], _, _, []).
get_vals_by_name([H|T], R, Row, [V|Rest]) :-
    nth1(Idx, R, H),
    nth1(Idx, Row, V),
    get_vals_by_name(T, R, Row, Rest).

% ---------------------------------------------------------------------
% 2. Core theory
% ---------------------------------------------------------------------
% bao dong thuoc tinh

xplus(_, F, X, Closure) :- xplus_iter(F, X, X, Closure).
xplus_iter(F, Current, Old, Closure) :-
    findall(Y, (member([LHS, Y], F), subset(LHS, Current)), Reached),
    flatten(Reached, ReachedFlat),
    union(Current, ReachedFlat, Next),
    sort(Next, NextSorted),
    (NextSorted = Old -> Closure = NextSorted ; xplus_iter(F, NextSorted, NextSorted, Closure)).
% -----

% inferenceFD(F, FD)
% Kiểm tra xem bảng dữ liệu hiện tại có thỏa mãn FD: LHS -> RHS không.
checkFD(R, LHS, RHS) :-
    % 1. Lấy tất cả các dòng dữ liệu (bỏ qua cột ID đầu tiên)
    findall(RowVals, (
        data(_ID, V1, V2, V3, V4, V5), 
        RowVals = [V1, V2, V3, V4, V5]
    ), AllRows),
    
    % 2. Dùng phép phủ định ( \+ ): Không tồn tại cặp dòng t1, t2 vi phạm
    \+ (
        member(T1, AllRows),
        member(T2, AllRows),
        T1 \= T2, % Hai dòng khác nhau
        
        % Lấy giá trị của vế trái (LHS) trên 2 dòng
        get_vals_by_name(LHS, R, T1, VL1),
        get_vals_by_name(LHS, R, T2, VL2),
        VL1 = VL2, % Nếu vế trái giống nhau...
        
        % Mà vế phải (RHS) lại khác nhau -> Vi phạm!
        get_vals_by_name(RHS, R, T1, VR1),
        get_vals_by_name(RHS, R, T2, VR2),
        VR1 \= VR2
    ).
%---
% Kiem tra sieu khoa (Superkey)
is_superkey(R, X, F) :-
    xplus(R, F, X, XP),
    forall(member(A, R), member(A, XP)).

% Tim mot khoa (Key)
find_one_key(R, F, K) :-
    subset_gen(R, K),
    K \= [],
    is_superkey(R, K, F),
    \+ is_not_minimal(R, F, K).

is_not_minimal(R, F, K) :-
    subset_gen(K, Ksub),
    Ksub \= K,
    Ksub \= [],
    is_superkey(R, Ksub, F).

% Kiem tra thuoc tinh khoa (Prime Attribute)
is_prime(A, AllKeys) :-
    member(Key, AllKeys),
    member(A, Key), !.

% FD Projection Chieu FD len luoc do con

projectFD(Ri, F, Fi) :-
    % 1. Lay tat ca cac tap con X cua Ri
    findall(X, (subset_gen(Ri, X), X \= [], X \= Ri), AllSubsets),
    
    % 2. Tim bao dong X+ (Dung _ de thay the Ri trong xplus) 
    findall([X, Y], (
        member(X, AllSubsets),
        xplus(_, F, X, XP),          
        intersection(XP, Ri, XP_Ri), 
        subtract(XP_Ri, X, Y),       
        Y \= []                      
    ), Fi_raw),
    
    sort(Fi_raw, Fi).
% ---------------------------------------------------------------------
% 3. Tim khoa va Normalform
% ---------------------------------------------------------------------

% Tim khoa (candkey/3)
candkey(R, F, OutKeys) :-
    var(OutKeys), !,
    setof(K, find_one_key(R, F, K), FoundList),
    print_key_list(FoundList),
    OutKeys = FoundList.

candkey(R, F, InKey) :-
    nonvar(InKey),
    find_one_key(R, F, InKey).

print_key_list([]).
print_key_list([H|T]) :-
    format(' + Key: ~w~n', [H]),
    print_key_list(T).

% =================================================================
% Kiem tra tuong duong
% =================================================================

% equivalent(F, G): True neu F và G tương đương
equivalent(F, G) :-
    is_covered(F, G), 
    is_covered(G, F). 

% is_covered(F, G): True neu moi FD trong F deu duoc bao dong boi G
is_covered(F, G) :-
    forall(
        member([X, Y], F),
        (xplus(_, G, X, XP_G), subset(Y, XP_G))
    ).

% Tim bao dong

mincover(F, MinF) :-
    % Buoc 1: Tach ve phai ve 1 tt
 
    findall([X, [A]], (member([X, RHS], F), member(A, RHS)), F1),
    
    % Bước 2: Left Reduction
    reduce_left(F1, F1, F2),
    
    % Bước 3: Right Reduction
    reduce_right(F2, F2, MinF_raw),
    sort(MinF_raw, MinF).

% --- Ho tro buoc 2 ---
reduce_left([], _, []).
reduce_left([[X, [A]]|T], FullF, [[NewX, [A]]|Rest]) :-
    find_min_lhs(X, A, FullF, NewX),
    reduce_left(T, FullF, Rest).

find_min_lhs(X, A, F, NewX) :-
    member(B, X),
    select(B, X, TempX),
    TempX \= [],
    % Kiem tra TempX co con suy ra duoc A khong
    xplus(_, F, TempX, XP),
    member(A, XP), !, 
    find_min_lhs(TempX, A, F, NewX).
find_min_lhs(X, _, _, X).

% --- Ho tro buoc 3: Khu FD du thua ---
reduce_right([], _, []).
reduce_right([FD|T], FullF, Rest) :-
    select(FD, FullF, TempF),
    [X, [A]] = FD,
    xplus(_, TempF, X, XP),
    member(A, XP), !, 
    reduce_right(T, TempF, Rest).
reduce_right([FD|T], FullF, [FD|Rest]) :-
    reduce_right(T, FullF, Rest).

%  2NF
is2NF(R, F) :-
    setof(K, find_one_key(R, F, K), AllKeys),
    \+ (
        member([LHS, RHS], F),
        member(A, RHS),
        \+ member(A, LHS),
        \+ is_prime(A, AllKeys),
        member(Key, AllKeys),
        subset_gen(Key, LHS),
        LHS \= Key,
        LHS \= []
    ).
%  3NF
is3NF(R, F) :-
    setof(K, find_one_key(R, F, K), AllKeys),
    \+ (
        member([LHS, RHS], F),
        member(A, RHS),
        \+ member(A, LHS),               % Non-trivial
        \+ is_superkey(R, LHS, F),       % Vế trái không là siêu khóa
        \+ is_prime(A, AllKeys)          % Vế phải không là thuộc tính khóa
    ).

%  BCNF
isBCNF(R, F) :-
    \+ (
        member([LHS, RHS], F),
        member(A, RHS),
        \+ member(A, LHS),               % Non-trivial
        \+ is_superkey(R, LHS, F)        % Vế trái không là siêu khóa
    ).

% Minimize Key
minimize_key([], _, _, []).
minimize_key([H|T], R, F, Result) :-
    append(T, [], CurrentSub),
    is_superkey(R, CurrentSub, F), !,
    minimize_key(T, R, F, Result).
minimize_key([H|T], R, F, [H|Result]) :-
    minimize_key(T, R, F, Result).


% Xac dinh Dang chuan cao nhat

normalF(R, F, 'BCNF') :- isBCNF(R, F), !.
normalF(R, F, '3NF')  :- is3NF(R, F), !.
normalF(R, F, '2NF')  :- is2NF(R, F), !.
normalF(_, _, '1NF'). % Mac dinh neu cac buoc tren deu sai


% Thuat toan Chase de kiem tra Lossless Join

% ham chinh de kiem tra Lossless Join

isLossChase(R, Decomp, F) :-
    init_matrix(R, Decomp, Matrix),
    chase_cycle(R, F, Matrix, FinalMatrix),
    check_all_a(FinalMatrix).

% 1. khoi ta matrix
init_matrix(R, Decomp, Matrix) :-
    length(R, LR),
    findall(Row, (nth1(RowIdx, Decomp, Ri), init_row(R, Ri, RowIdx, LR, Row)), Matrix).

init_row([], _, _, _, []).
init_row([H|T], Ri, RowIdx, LR, [Val|RowRest]) :-
    length([H|T], CurrentL),
    ColIdx is LR - CurrentL + 1,
    (member(H, Ri) -> Val = a(ColIdx) ; Val = b(RowIdx, ColIdx)),
    init_row(T, Ri, RowIdx, LR, RowRest).

% 2. vong lap chinh - Chase Cycle
chase_cycle(R, F, Matrix, FinalMatrix) :-
    one_pass(R, F, Matrix, NextMatrix),
    (Matrix == NextMatrix -> 
        FinalMatrix = Matrix 
    ;   chase_cycle(R, F, NextMatrix, FinalMatrix)
    ).

% Quet qua cac FD va ap dung len ma tran
one_pass(_, [], M, M).
one_pass(R, [FD|Rest], M, FinalM) :-
    apply_fd(R, FD, M, M1),
    one_pass(R, Rest, M1, FinalM).

% FD: [LHS, RHS]
apply_fd(R, [LHS, RHS], Matrix, NewMatrix) :-
    get_indices(LHS, R, LHSIdxs),
    get_indices(RHS, R, RHSIdxs),
    update_matrix_by_fd(LHSIdxs, RHSIdxs, Matrix, NewMatrix).

update_matrix_by_fd(LHSIdxs, RHSIdxs, Matrix, NewMatrix) :-
    maplist(get_cols(LHSIdxs), Matrix, LHSValues),
    sort(LHSValues, UniqueLHS),
    do_unify(UniqueLHS, LHSIdxs, RHSIdxs, Matrix, NewMatrix).

do_unify([], _, _, M, M).
do_unify([V|Vs], LHSIdxs, RHSIdxs, M, FinalM) :-
    findall(Row, (member(Row, M), get_cols(LHSIdxs, Row, V)), TargetRows),
    find_best_rhs(RHSIdxs, TargetRows, BestRHS),
    update_rows(V, LHSIdxs, RHSIdxs, BestRHS, M, M1),
    do_unify(Vs, LHSIdxs, RHSIdxs, M1, FinalM).

% Tim gia tri tot nhat cho cac cot RHS (a(j))
find_best_rhs([], _, []).
find_best_rhs([Idx|Rest], Rows, [Best|BestRest]) :-
    findall(Val, (member(R, Rows), nth1(Idx, R, Val)), Vals),
    (member(a(Idx), Vals) -> Best = a(Idx) ; (sort(Vals, [Best|_])), !),
    find_best_rhs(Rest, Rows, BestRest).

% Cap nhat cac dong co cung gia tri LHS
update_rows(_, _, _, _, [], []).
update_rows(V, LHSIdxs, RHSIdxs, BestRHS, [Row|Rest], [NewRow|NewRest]) :-
    get_cols(LHSIdxs, Row, V), !,
    replace_multiple(Row, RHSIdxs, BestRHS, NewRow),
    update_rows(V, LHSIdxs, RHSIdxs, BestRHS, Rest, NewRest).
update_rows(V, LHSIdxs, RHSIdxs, BestRHS, [Row|Rest], [Row|NewRest]) :-
    update_rows(V, LHSIdxs, RHSIdxs, BestRHS, Rest, NewRest).

% 3. Helpers
get_cols(Idxs, Row, Values) :- findall(V, (member(I, Idxs), nth1(I, Row, V)), Values).

replace_multiple(Row, [], [], Row).
replace_multiple(Row, [Idx|Idxs], [Val|Vals], FinalRow) :-
    replace_nth(Row, Idx, Val, TempRow),
    replace_multiple(TempRow, Idxs, Vals, FinalRow).

replace_nth([_|T], 1, Val, [Val|T]) :- !.
replace_nth([H|T], I, Val, [H|R]) :- I > 1, I1 is I - 1, replace_nth(T, I1, Val, R).

get_indices(Attrs, R, Idxs) :- findall(Idx, (member(A, Attrs), nth1(Idx, R, A)), Idxs).

check_all_a(Matrix) :- 
    member(Row, Matrix), 
    forall(member(V, Row), (V = a(_))), !.


% decomp_report(R, F)
decomposition(R, F) :-
    writeln('--- BCNF Decomposition ---'),
  
    bcnf_decomp_enhanced(R, F, DecompList),

    print_decomp_results(DecompList),
    
    check_preservation_from_list(R, F, DecompList),
    !.

% bcnf_decomp_enhanced
bcnf_decomp_enhanced(R, F, [[R, F]]) :- 
    isBCNF(R, F), !.

bcnf_decomp_enhanced(R, F, Result) :-
    member([LHS, RHS], F),
    member(A, RHS),
    \+ member(A, LHS),
    \+ is_superkey(R, LHS, F),
    !,

    union(LHS, [A], R1),
    delete(R, A, R2),
 
    projectFD(R1, F, F1),
    projectFD(R2, F, F2),

    bcnf_decomp_enhanced(R1, F1, Res1),
    bcnf_decomp_enhanced(R2, F2, Res2),
    append(Res1, Res2, Result).

print_decomp_results([]).
print_decomp_results([[Ri, Fi]|T]) :-
    sort(Ri, SortedRi),               % sap xep thuoc tinh (Ví dụ [c,b] -> [b,c])
    format(' + Sub-schema: ~w~n', [SortedRi]),
    format('   FDs on this schema: ~w~n', [Fi]),
    print_decomp_results(T).

check_preservation_from_list(R, F, DecompList) :-
    findall(Fi, member([_, Fi], DecompList), AllFi),
    flatten(AllFi, G_raw),
    sort(G_raw, G),
    (   forall(member([LHS, RHS], F), (xplus(R, G, LHS, XP_G), subset(RHS, XP_G)))
    ->  writeln(' + Dependency Preservation Satisfied !!')
    ;   writeln(' + Dependency Preservation Failed !!')
    ).