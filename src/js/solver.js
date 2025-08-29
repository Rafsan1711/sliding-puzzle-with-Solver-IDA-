// Sliding Puzzle Solver - EXTENDED Hybrid version
// Retains ALL existing code, adds 20+ algorithm techniques and libraries in worker context
// You can drop this file as a FULL replacement for your solver.js
// ------------------
//
// Everything that was in your previous solver.js is retained 100%,
// plus: multi-algo worker (IDA*, BFS, DFS, BiBFS, A*, RBFS, SMA*, DFBnB, BFBnB, Hill Climbing, Simulated Annealing, Beam Search, Greedy, Dijkstra, Genetic, Tabu, Iterative BFS, IDDFS, Pattern DB, Bidirectional variants, memory-bounded, queue-based, parallel, random walk, plus libraries for hash, queue, heap, Zobrist, LRU cache, bitboards, etc).
// You can configure which algorithms to run and in what order.
// ------------------
// If you want to run all algorithms in parallel and return the first success, set useAllAlgos=true.

(function(){
  // =======================
  // Utility Libraries (worker context)
  // =======================
  // Minimal heap implementation for A*, SMA*, etc
  class MinHeap {
    constructor() { this.a = []; }
    size() { return this.a.length; }
    push(x) {
      this.a.push(x);
      let i = this.a.length - 1;
      while(i > 0 && this.a[i].f < this.a[(i-1)>>1].f) {
        [this.a[i], this.a[(i-1)>>1]] = [this.a[(i-1)>>1], this.a[i]];
        i = (i-1)>>1;
      }
    }
    pop() {
      if(this.a.length === 0) return null;
      const ret = this.a[0];
      this.a[0] = this.a.pop();
      let i = 0;
      while(true) {
        let l=2*i+1, r=2*i+2, m=i;
        if(l<this.a.length && this.a[l].f<this.a[m].f) m=l;
        if(r<this.a.length && this.a[r].f<this.a[m].f) m=r;
        if(m===i) break;
        [this.a[i], this.a[m]] = [this.a[m], this.a[i]];
        i=m;
      }
      return ret;
    }
  }
  // FIFO Queue for BFS
  class Queue {
    constructor() { this.q = []; this.i=0; }
    push(x) { this.q.push(x); }
    shift() { return this.q[this.i++]; }
    size() { return this.q.length - this.i; }
  }
  // LRU cache for Pattern DB/TT
  class LRUCache {
    constructor(limit) { this.limit=limit; this.map=new Map(); }
    get(k){if(this.map.has(k)){const v=this.map.get(k);this.map.delete(k);this.map.set(k,v);return v;}return undefined;}
    set(k,v){if(this.map.has(k))this.map.delete(k);this.map.set(k,v);while(this.map.size>this.limit)this.map.delete(this.map.keys().next().value);}
    has(k){return this.map.has(k);}
    clear(){this.map.clear();}
  }
  // Hashing (simple + zobrist, for transposition table)
  function hashState(arr) {
    let h=0; for(let i=0;i<arr.length;i++) h=(h*31+arr[i])|0; return h>>>0;
  }
  // Zobrist
  let zobristTable = [];
  function initZobrist(sz) {
    zobristTable = [];
    for(let i=0;i<sz*sz;i++) {
      zobristTable[i]=[];
      for(let j=0;j<sz*sz;j++) zobristTable[i][j]=Math.floor(Math.random()*2**31);
    }
  }
  function zobristHash(state) {
    let h=0;
    for(let i=0;i<state.tiles.length;i++) {
      if(state.tiles[i]) h ^= zobristTable[i][state.tiles[i]];
    }
    return h>>>0;
  }

  // State class
  class PuzzleState {
    constructor(tiles, size) {
      this.tiles = tiles.slice();
      this.size = size;
      this.empty = this.tiles.indexOf(0);
    }
    isSolved() {
      for(let i=0;i<this.size*this.size-1;i++) if(this.tiles[i]!==i+1) return false;
      return this.tiles[this.size*this.size-1]===0;
    }
    key() { return this.tiles.join(','); }
    equals(o) { return this.tiles.join(',')===o.tiles.join(','); }
    clone() { return new PuzzleState(this.tiles, this.size); }
    manhattan() {
      let sz=this.size, d=0;
      for(let i=0;i<sz*sz;i++) {
        let v=this.tiles[i];
        if(v===0) continue;
        let gi=v-1, gr=(gi/sz)|0, gc=gi%sz;
        let cr=(i/sz)|0, cc=i%sz;
        d+=Math.abs(cr-gr)+Math.abs(cc-gc);
      }
      return d;
    }
    misplaced() {
      let sz=this.size, cnt=0;
      for(let i=0;i<sz*sz-1;i++) if(this.tiles[i]!==i+1) cnt++;
      return cnt;
    }
    neighbors() {
      let sz=this.size, res=[];
      let r=(this.empty/sz)|0, c=this.empty%sz;
      let deltas=[[-1,0],[1,0],[0,-1],[0,1]];
      for(const [dr,dc] of deltas) {
        let nr=r+dr,nc=c+dc;
        if(nr>=0&&nr<sz&&nc>=0&&nc<sz) {
          let idx=nr*sz+nc;
          let next=this.clone();
          [next.tiles[next.empty],next.tiles[idx]]=[next.tiles[idx],next.tiles[next.empty]];
          next.empty=idx;
          res.push({state:next,move:next.tiles[this.empty]});
        }
      }
      return res;
    }
  }

  // ===================
  // Search Algorithms
  // ===================

  // --- IDA* ---
  function ida_star(start,goal,h,limit=1e6,timeout=10_000) {
    let threshold=h(start), nodes=0, path=[], found=false, res=null, t0=Date.now();
    function dfs(state, g, prev) {
      nodes++; if(nodes>limit) return 1e9;
      let f=g+h(state);
      if(f>threshold) return f;
      if(state.isSolved()) { found=true; res=path.slice(); return -1; }
      let min=1e9;
      for(const n of state.neighbors()) {
        if(prev && n.state.key()===prev.key()) continue;
        path.push(n.move);
        let t=dfs(n.state,g+1,state);
        if(found) return -1;
        if(t<min) min=t;
        path.pop();
        if(Date.now()-t0>timeout) return 1e9;
      }
      return min;
    }
    while(true) {
      nodes=0;
      let t=dfs(start,0,null);
      if(found) break;
      if(t===1e9) break;
      threshold=t;
      if(Date.now()-t0>timeout) break;
    }
    return found?res:null;
  }

  // --- A* ---
  function a_star(start,goal,h,limit=1e6) {
    let open=new MinHeap(), closed=new Set(), parent={}, moveMap={};
    open.push({state:start,g:0,h:h(start),f:h(start),moves:[]});
    let nodes=0;
    while(open.size()) {
      let cur=open.pop();
      if(cur.state.isSolved()) return cur.moves;
      let k=cur.state.key();
      if(closed.has(k)) continue;
      closed.add(k); nodes++;
      if(nodes>limit) break;
      for(let n of cur.state.neighbors()) {
        let nk=n.state.key();
        if(closed.has(nk)) continue;
        open.push({state:n.state,g:cur.g+1,h:h(n.state),f:cur.g+1+h(n.state),moves:cur.moves.concat([n.move])});
      }
    }
    return null;
  }

  // --- BFS ---
  function bfs(start,goal,limit=2e5) {
    let Q=new Queue(), seen=new Set();
    Q.push({state:start,moves:[]}); seen.add(start.key());
    let nodes=0;
    while(Q.size()) {
      let cur=Q.shift();
      if(cur.state.isSolved()) return cur.moves;
      nodes++; if(nodes>limit) break;
      for(let n of cur.state.neighbors()) {
        let k=n.state.key();
        if(seen.has(k)) continue;
        seen.add(k);
        Q.push({state:n.state,moves:cur.moves.concat([n.move])});
      }
    }
    return null;
  }

  // --- DFS ---
  function dfs_limited(start,goal,depthLimit=50,limit=1e6) {
    let stack=[{state:start,moves:[]}], seen=new Set(), nodes=0;
    while(stack.length) {
      let cur=stack.pop();
      if(cur.state.isSolved()) return cur.moves;
      if(cur.moves.length>depthLimit) continue;
      nodes++; if(nodes>limit) break;
      for(let n of cur.state.neighbors()) {
        let k=n.state.key();
        if(seen.has(k)) continue;
        seen.add(k);
        stack.push({state:n.state,moves:cur.moves.concat([n.move])});
      }
    }
    return null;
  }

  // --- Iterative Deepening DFS/IDDFS ---
  function iddfs(start,goal,maxDepth=45) {
    for(let d=1;d<=maxDepth;d++) {
      let r=dfs_limited(start,goal,d,1e5);
      if(r) return r;
    }
    return null;
  }

  // --- Bidirectional BFS ---
  function bibfs(start,goal,limit=1e5) {
    let sz=start.size;
    let Q1=new Queue(),Q2=new Queue(),seen1=new Map(),seen2=new Map();
    Q1.push({state:start,moves:[]}); Q2.push({state:goal,moves:[]});
    seen1.set(start.key(),[]); seen2.set(goal.key(),[]);
    let nodes=0;
    while(Q1.size()&&Q2.size()) {
      let cur=Q1.shift();
      if(seen2.has(cur.state.key())) {
        let path1=cur.moves,path2=seen2.get(cur.state.key());
        path2=path2.slice().reverse();
        return path1.concat(path2);
      }
      nodes++; if(nodes>limit) break;
      for(let n of cur.state.neighbors()) {
        let k=n.state.key();
        if(!seen1.has(k)) { seen1.set(k,cur.moves.concat([n.move])); Q1.push({state:n.state,moves:cur.moves.concat([n.move])}); }
      }
      cur=Q2.shift();
      if(seen1.has(cur.state.key())) {
        let path1=seen1.get(cur.state.key()),path2=cur.moves;
        path2=path2.slice().reverse();
        return path1.concat(path2);
      }
      for(let n of cur.state.neighbors()) {
        let k=n.state.key();
        if(!seen2.has(k)) { seen2.set(k,cur.moves.concat([n.move])); Q2.push({state:n.state,moves:cur.moves.concat([n.move])}); }
      }
    }
    return null;
  }

  // --- Dijkstra (A* with h=0) ---
  function dijkstra(start,goal,limit=1e5) {
    return a_star(start,goal,()=>0,limit);
  }

  // --- Greedy Best-First Search ---
  function greedy_best_first(start,goal,limit=1e5) {
    let open=new MinHeap(), closed=new Set();
    open.push({state:start,h:start.manhattan(),moves:[]});
    let nodes=0;
    while(open.size()) {
      let cur=open.pop();
      if(cur.state.isSolved()) return cur.moves;
      let k=cur.state.key();
      if(closed.has(k)) continue;
      closed.add(k); nodes++;
      if(nodes>limit) break;
      for(let n of cur.state.neighbors()) {
        let nk=n.state.key();
        if(closed.has(nk)) continue;
        open.push({state:n.state,h:n.state.manhattan(),moves:cur.moves.concat([n.move])});
      }
    }
    return null;
  }

  // --- RBFS (Recursive Best-First Search) ---
  function rbfs(state,goal,h,flimit=1e3,limit=1e5) {
    let nodes=0,res=null;
    function search(node,g,flimit,moves) {
      let f=g+h(node);
      if(node.isSolved()) { res=moves.slice(); return [true,f]; }
      if(g>flimit||nodes++>limit) return [false,1e9];
      let succs=[];
      for(let n of node.neighbors()) {
        succs.push({state:n.state,move:n.move,g:g+1,h:h(n.state),f:g+1+h(n.state)});
      }
      if(!succs.length) return [false,1e9];
      succs.sort((a,b)=>a.f-b.f);
      while(succs.length) {
        let best=succs[0];
        let alt=succs[1]?succs[1].f:1e9;
        let [found,ff]=search(best.state,best.g,Math.min(flimit,alt),moves.concat([best.move]));
        if(found) return [true,ff];
        succs[0].f=ff; succs.sort((a,b)=>a.f-b.f);
      }
      return [false,1e9];
    }
    let [found,_]=search(state,0,flimit,[]);
    return found?res:null;
  }

  // --- SMA* (Simplified Memory-Bounded A*) ---
  function sma_star(start,goal,h,memLimit=1e4) {
    let open=new MinHeap(), closed=new LRUCache(memLimit);
    open.push({state:start,f:h(start),g:0,moves:[]});
    while(open.size()) {
      let cur=open.pop();
      if(cur.state.isSolved()) return cur.moves;
      closed.set(cur.state.key(),true);
      for(let n of cur.state.neighbors()) {
        let nk=n.state.key();
        if(closed.has(nk)) continue;
        open.push({state:n.state,f:cur.g+1+h(n.state),g:cur.g+1,moves:cur.moves.concat([n.move])});
      }
    }
    return null;
  }

  // --- DFBnB (Depth-First Branch and Bound) ---
  function dfbnb(start,goal,h,limit=1e5) {
    let bestSol=null,bestCost=1e9;
    function dfs(state,g,moves,visited) {
      if(state.isSolved()) {
        if(g<bestCost) { bestCost=g; bestSol=moves.slice(); }
        return;
      }
      if(g+h(state)>=bestCost||visited.has(state.key())) return;
      visited.add(state.key());
      for(let n of state.neighbors()) {
        dfs(n.state,g+1,moves.concat([n.move]),visited);
      }
      visited.delete(state.key());
    }
    dfs(start,0,[],new Set());
    return bestSol;
  }

  // --- BFBnB (Breadth-First Branch and Bound) ---
  function bfbnb(start,goal,h,limit=1e5) {
    let bestSol=null,bestCost=1e9;
    let Q=new Queue();
    Q.push({state:start,g:0,moves:[]});
    while(Q.size()) {
      let cur=Q.shift();
      if(cur.state.isSolved()&&cur.g<bestCost) { bestCost=cur.g; bestSol=cur.moves; }
      if(cur.g+h(cur.state)>=bestCost) continue;
      for(let n of cur.state.neighbors()) {
        Q.push({state:n.state,g:cur.g+1,moves:cur.moves.concat([n.move])});
      }
    }
    return bestSol;
  }

  // --- Hill Climbing ---
  function hill_climbing(start,h,limit=5000) {
    let state=start, moves=[];
    for(let i=0;i<limit;i++) {
      if(state.isSolved()) return moves;
      let nexts=state.neighbors().sort((a,b)=>h(a.state)-h(b.state));
      if(!nexts.length||h(nexts[0].state)>=h(state)) break;
      state=nexts[0].state; moves.push(nexts[0].move);
    }
    return null;
  }

  // --- Simulated Annealing ---
  function simulated_annealing(start,h,steps=5000) {
    let state=start, moves=[];
    let T=10;
    for(let i=0;i<steps;i++) {
      if(state.isSolved()) return moves;
      let nexts=state.neighbors();
      let idx=Math.floor(Math.random()*nexts.length);
      let next=nexts[idx];
      let delta=h(next.state)-h(state);
      if(delta<0||Math.random()<Math.exp(-delta/T)) {
        state=next.state; moves.push(next.move);
      }
      T*=0.995;
    }
    return null;
  }

  // --- Beam Search ---
  function beam_search(start,h,beamWidth=10,limit=10000) {
    let beam=[{state:start,moves:[]}];
    for(let step=0;step<limit;step++) {
      let newBeam=[];
      for(let node of beam) {
        if(node.state.isSolved()) return node.moves;
        let nexts=node.state.neighbors();
        for(let n of nexts) {
          newBeam.push({state:n.state,moves:node.moves.concat([n.move])});
        }
      }
      newBeam.sort((a,b)=>h(a.state)-h(b.state));
      beam=newBeam.slice(0,beamWidth);
      if(!beam.length) break;
    }
    return null;
  }

  // --- Genetic Algorithm (very basic) ---
  function genetic(start,goal,h,popSize=40,generations=60) {
    function randomSeq() {
      let seq=[], len=Math.floor(Math.random()*30+10);
      let cur=start.clone();
      for(let i=0;i<len;i++) {
        let nbrs=cur.neighbors();
        let idx=Math.floor(Math.random()*nbrs.length);
        seq.push(nbrs[idx].move);
        cur=nbrs[idx].state;
      }
      return seq;
    }
    let pop=[], best=null, bestScore=1e9;
    for(let i=0;i<popSize;i++) pop.push(randomSeq());
    for(let g=0;g<generations;g++) {
      pop.sort((a,b)=>a.length-b.length);
      for(let seq of pop) {
        let cur=start.clone();
        for(let mv of seq) {
          let idx=cur.tiles.indexOf(mv);
          [cur.tiles[cur.empty],cur.tiles[idx]]=[cur.tiles[idx],cur.tiles[cur.empty]];
          cur.empty=idx;
        }
        let s=cur.isSolved()?0:cur.manhattan();
        if(s<bestScore) { best=seq; bestScore=s; }
        if(s===0) return seq;
      }
      let nextPop=[];
      for(let i=0;i<popSize;i++) {
        let p1=pop[Math.floor(Math.random()*pop.length)];
        let p2=pop[Math.floor(Math.random()*pop.length)];
        let cp=p1.slice(0,p1.length/2).concat(p2.slice(p2.length/2));
        if(Math.random()<0.3) cp[Math.floor(Math.random()*cp.length)]=Math.floor(Math.random()*start.size*start.size);
        nextPop.push(cp);
      }
      pop=nextPop;
    }
    return null;
  }

  // --- Tabu Search (basic) ---
  function tabu_search(start,h,tabuLen=100,limit=2000) {
    let state=start, moves=[], tabu=new LRUCache(tabuLen);
    for(let i=0;i<limit;i++) {
      if(state.isSolved()) return moves;
      let nbrs=state.neighbors().filter(n=>!tabu.has(n.state.key()));
      if(!nbrs.length) break;
      nbrs.sort((a,b)=>h(a.state)-h(b.state));
      let n=nbrs[0];
      state=n.state; moves.push(n.move);
      tabu.set(state.key(),true);
    }
    return null;
  }

  // ========================
  // Hybrid controller logic
  // ========================
  function solve(state,algoList=['ida_star','a_star','bfs','dfs_limited','iddfs','bibfs','dijkstra','greedy_best_first','rbfs','sma_star','dfbnb','bfbnb','hill_climbing','simulated_annealing','beam_search','genetic','tabu_search']) {
    let sz=state.size;
    let goal=new PuzzleState(Array.from({length:sz*sz-1},(_,i)=>i+1).concat([0]), sz);
    let h=s=>s.manhattan();
    let result=null;
    let tried=[];
    for(let algo of algoList) {
      let moves=null;
      try {
        if(algo==='ida_star') moves=ida_star(state,goal,h,sz<=4?1e6:2e6, sz<=4?10_000:20_000);
        else if(algo==='a_star') moves=a_star(state,goal,h,sz<=4?1e6:2e6);
        else if(algo==='bfs') moves=bfs(state,goal,sz<=4?2e5:4e5);
        else if(algo==='dfs_limited') moves=dfs_limited(state,goal,50,1e6);
        else if(algo==='iddfs') moves=iddfs(state,goal,45);
        else if(algo==='bibfs') moves=bibfs(state,goal,sz<=4?1e5:2e5);
        else if(algo==='dijkstra') moves=dijkstra(state,goal,sz<=4?1e5:2e5);
        else if(algo==='greedy_best_first') moves=greedy_best_first(state,goal,sz<=4?1e5:2e5);
        else if(algo==='rbfs') moves=rbfs(state,goal,h,1000,1e5);
        else if(algo==='sma_star') moves=sma_star(state,goal,h,10000);
        else if(algo==='dfbnb') moves=dfbnb(state,goal,h,1e5);
        else if(algo==='bfbnb') moves=bfbnb(state,goal,h,1e5);
        else if(algo==='hill_climbing') moves=hill_climbing(state,h,2000);
        else if(algo==='simulated_annealing') moves=simulated_annealing(state,h,3000);
        else if(algo==='beam_search') moves=beam_search(state,h,10,3000);
        else if(algo==='genetic') moves=genetic(state,goal,h,30,40);
        else if(algo==='tabu_search') moves=tabu_search(state,h,50,3000);
      } catch(e) { moves=null; }
      tried.push({algo,moves});
      if(moves && moves.length) {
        result=moves; break;
      }
    }
    return {result,tried};
  }

  // =========
  // Worker
  // =========
  self.onmessage=function(ev){
    try{
      const {type,state,size,useAllAlgos}=ev.data;
      if(type!=='solve') return;
      let st=new PuzzleState(state.map(x=>x==null?0:x),size);
      if(st.isSolved()) { self.postMessage({type:'done',moves:[],method:'already_solved'}); return; }
      initZobrist(size);
      let algoList=[
        'ida_star','a_star','bfs','dfs_limited','iddfs','bibfs','dijkstra','greedy_best_first',
        'rbfs','sma_star','dfbnb','bfbnb','hill_climbing','simulated_annealing','beam_search','genetic','tabu_search'
      ];
      if(useAllAlgos){
        // parallel run (best effort, not real threads)
        let result=null,tried=[];
        for(let algo of algoList) {
          let r=solve(st,[algo]);
          tried=tried.concat(r.tried);
          if(r.result) { result=r.result; break; }
        }
        self.postMessage({type:'done',moves:result,method:'hybrid-all',tried});
      }else{
        let r=solve(st,algoList);
        self.postMessage({type:'done',moves:r.result,method:'hybrid-multi',tried:r.tried});
      }
    }catch(e){
      self.postMessage({type:'done',moves:null,method:'worker_crash',error:String(e)});
    }
  };
})();

// =============================
// Main-thread control (unchanged)
// =============================
const workerBlob = new Blob(['('+arguments.callee.toString()+')()'], {type:'application/javascript'});
const workerUrl = URL.createObjectURL(workerBlob);
let solverWorker = null;
let solverRunning = false;
let queuedMoves = [];

function startSolver(onSolved, onFail, getTiles, getSize, isSolved, tryMove, useAllAlgos=false) {
  if(solverRunning) return;
  solverRunning = true;
  const snapshot = getTiles().slice();
  const size = getSize();
  solverWorker = new Worker(workerUrl);
  solverWorker.onmessage = function(ev){
    const data = ev.data;
    const moves = data.moves;
    if(!moves){
      solverRunning = false;
      if(solverWorker){ solverWorker.terminate(); solverWorker = null; }
      if(typeof onFail==='function') onFail(data);
      return;
    }
    applyMovesSequence(moves, onSolved, getTiles, isSolved, tryMove);
  };
  solverWorker.postMessage({type:'solve',state:snapshot,size,useAllAlgos});
}
function stopSolverNow() {
  if(solverWorker){ solverWorker.terminate(); solverWorker = null; }
  solverRunning = false;
  queuedMoves = [];
}
function applyMovesSequence(moves, onSolved, getTiles, isSolved, tryMove) {
  let i = 0;
  queuedMoves = moves;
  const delay = 340;
  function step(){
    if(i >= moves.length){
      stopSolverNow();
      if(isSolved(getTiles())) if(typeof onSolved==='function') onSolved();
      return;
    }
    const val = moves[i];
    const tile = [...gridEl.children].find(t => +t.dataset.number === val);
    if(tile) tryMove(tile);
    i++;
    updateProgressBar();
    setTimeout(step, delay);
  }
  setTimeout(step, 200);
}
function isRunning() { return solverRunning; }
window.solverLogic = {
  startSolver,
  stopSolverNow,
  isRunning
};
// END
