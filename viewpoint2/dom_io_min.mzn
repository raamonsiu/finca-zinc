include "globals.mzn";

function var int: linearToRow(var int: p) = (p - 1) div width + 1;
function var int: linearToCol(var int: p) = (p - 1) mod width + 1;

% Specification of estate types
int: n_tipus_finques; % n_tipus_finques means number of estate types
set of int: Tipus_Finca = 1..n_tipus_finques; % Tipus_Finca is the domain of estate type IDs

type Pos = tuple(int,int);
Pos: PAD = (0,0); % PAD marks unused cells in shape definitions

int: maxPts; % maxPts means max cells used to define one estate type

array[Tipus_Finca, 1..maxPts] of Pos: definicio_finques; % definicio_finques stores relative shape cells per estate type

% Buildable plot dimensions
int: height; % height means board height
int: width; % width means board width

% Cells reserved for parks
set of int: parcs; % parcs means linear indexes of park cells

% Cells reserved for paths
set of int: camins; % camins means linear indexes of path cells

% Estates to place, indicating their type
int: n_finques; % n_finques means number of estates to place
array[1..n_finques] of Tipus_Finca: finques; % finques maps each estate index to its type

% Pairs of estates that cannot touch
set of int: Index_Finca = 1..n_finques; % Index_Finca is the set of estate indexes

int: n_incompatibles; % n_incompatibles means number of incompatible estate pairs
type Incompatibles = tuple(Index_Finca, Index_Finca);

array[1..n_incompatibles] of Incompatibles: incompatibles; % incompatibles stores estate index pairs that cannot touch

% Estates that must have at least one adjacent park cell
set of Index_Finca: finques_amb_parc; % finques_amb_parc are estates that must touch a park

% Input constraints

array[Index_Finca] of int: npts = % npts is the number of occupied cells for each estate
  [ sum(i in 1..maxPts)( bool2int(definicio_finques[finques[k], i] != PAD) )
  | k in Index_Finca ];

int: N = sum(npts); % N is total occupied cells from all estates

constraint N <= height*width; % This does not account for parks and paths

% CONSTRAINTS

array[1..N] of var 1..height*width: solucio; % solucio assigns a board position to each occupied cell slot

% All estates must be placed
constraint alldifferent(solucio);

% Each piece must be placed according to definicio_finques
array[Index_Finca] of int: start = [ 1 + sum(t in 1..k-1)(npts[t]) | k in Index_Finca ]; 
function set of int: idxs(int: k) = start[k] .. start[k] + npts[k] - 1;

type D = tuple(int,int);

function var D: distancia(var int: a, var int: b) =
  ( abs(linearToRow(a) - linearToRow(b)),
    abs(linearToCol(a) - linearToCol(b)) );


function array[1..2] of D: possibles_distancies(int: k, int: i, int: j) =
  let {
    Tipus_Finca: t = finques[k],
    Pos: a = definicio_finques[t, i],
    Pos: b = definicio_finques[t, j],
    int: dr = abs(a.1 - b.1),
    int: dc = abs(a.2 - b.2)
  } in
    [ (dr, dc), (dc, dr) ];



function int: local_idx(int: k, int: g) = g - start[k] + 1;

constraint forall(k in Index_Finca)(
  forall(i, j in idxs(k) where i < j)(
    let {
      int: li = local_idx(k,i),
      int: lj = local_idx(k,j),
      var D: d = distancia(solucio[i], solucio[j]),
      array[1..2] of D: P = possibles_distancies(k, li, lj)
    } in
      (d == P[1]) \/ (d == P[2])
  )
);


% Must not be parks or paths
set of int: forb = parcs union camins; % forb is the set of forbidden cells for estates
constraint forall(p in 1..N)(not (solucio[p] in forb) );


% Incompatibilities
function var bool: adjacent4(var int: a, var int: b) =
  abs(linearToRow(a) - linearToRow(b)) + abs(linearToCol(a) - linearToCol(b)) == 1;

constraint forall(m in 1..n_incompatibles)(
  let {
    int: k1 = incompatibles[m].1,
    int: k2 = incompatibles[m].2
  } in
  forall(p1 in idxs(k1), p2 in idxs(k2))(
    not adjacent4(solucio[p1], solucio[p2])
  )
);

% estates with park

constraint forall(k in finques_amb_parc)(
  exists(p in idxs(k), q in parcs)(
    adjacent4(solucio[p], q)
  )
);



solve :: int_search(solucio, input_order, indomain_min) satisfy;



% OUTPUT

function int: rcToLinear(int: r, int: c) = (r - 1) * width + c;

function var 0..n_finques: finca_of_point(var 1..N: p) =
  sum(k in Index_Finca)(
    bool2int(p >= start[k] /\ p <= start[k] + npts[k] - 1) * k
  );

array[1..height, 1..width] of var 0..N: grid =
  array2d(1..height, 1..width,
    [ if exists(k in 1..N)(linearToRow(solucio[k]) == r /\ linearToCol(solucio[k]) == c)
      then sum(k in 1..N)(
             bool2int(linearToRow(solucio[k]) == r /\ linearToCol(solucio[k]) == c) * k
           )
      else 0
      endif
    | r in 1..height, c in 1..width ]);

output [
  "Llegenda: P=parc, C=cami, .=buit, numeros=tipus de finca\n",
  "Graella:\n",
  concat([ concat([
    let {
      int: lin = rcToLinear(r,c),
      int: p = fix(grid[r,c])
    } in
      if lin in parcs then " P "
      elseif lin in camins then " C "
      elseif p == 0 then " . "
      else
        let { int: v = fix(finques[finca_of_point(p)]) } in
          (if v < 10 then " " else "" endif) ++ show(v) ++ " "
      endif
  | c in 1..width ]) ++ "\n"
  | r in 1..height ])
];







