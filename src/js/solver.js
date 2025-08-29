// Solver logic and Web Worker for Sliding Puzzle

function solverWorkerFunction(){
  self.onmessage = function(ev){
    try{
      const {type, state, size} = ev.data;
      if(type !== 'solve') return;
      const startState = state.slice();

      function idxToRC(i){ return {r: Math.floor(i/size), c: i%size}; }
      const goalPos = {}; for(let v=1; v<=size*size-1; v++) goalPos[v] = idxToRC(v-1);

      function manhattanUnfixed(arr, fixedSet){
        let s = 0;
        for(let i=0;i<arr.length;i++){
          const v = arr[i]; if(v==null) continue;
          const gi = v-1; if(fixedSet && fixedSet.has(gi)) continue;
          const cur = idxToRC(i), g = goalPos[v];
          if(!g) continue;
          s += Math.abs(cur.r - g.r) + Math.abs(cur.c - g.c);
        }
        return s;
      }

      function neighborsOfEmpty(emptyIdx){
        const res=[];
        const r=Math.floor(emptyIdx/size), c=emptyIdx%size;
        const deltas=[{dr:-1,dc:0},{dr:1,dc:0},{dr:0,dc:-1},{dr:0,dc:1}];
        for(const d of deltas){
          const nr=r+d.dr, nc=c+d.dc;
          if(nr>=0 && nr<size && nc>=0 && nc<size) res.push(nr*size+nc);
        }
        return res;
      }

      function idaPlaceTarget(currentState, fixedSet, targetVal, targetGoalIdx, nodeCap=600_000, tCap=10_000){
        const state = currentState.slice();
        let empty = state.indexOf(null);
        let nodes=0;
        function h(){ return manhattanUnfixed(state, fixedSet); }
        let threshold = h();
        const path = [];
        let found=null;
        function dfs(eidx, g, prev){
          nodes++;
          if(nodes>nodeCap) return Infinity;
          const hv = manhattanUnfixed(state, fixedSet);
          const f = g + hv;
          if(f > threshold) return f;
          if(state[targetGoalIdx] === targetVal) { found = path.slice(); return 'FOUND'; }
          let min=Infinity;
          const neigh = neighborsOfEmpty(eidx);
          const order = neigh.map(idx=>{
            if(fixedSet.has(idx)) return {idx, hv2: 1e9};
            const val = state[idx];
            state[eidx]=val; state[idx]=null;
            const hv2 = manhattanUnfixed(state, fixedSet);
            state[idx]=val; state[eidx]=null;
            return {idx, hv2};
          }).filter(Boolean).sort((a,b)=>a.hv2-b.hv2);
          for(const o of order){
            const ti = o.idx;
            if(prev !== undefined && ti === prev) continue;
            if(fixedSet.has(ti)) continue;
            const v = state[ti];
            state[eidx] = v; state[ti] = null;
            path.push(v);
            const r = dfs(ti, g+1, eidx);
            if(r === 'FOUND') return 'FOUND';
            if(r < min) min = r;
            path.pop();
            state[ti] = v; state[eidx] = null;
          }
          return min;
        }
        const t0 = Date.now();
        while(true){
          nodes=0;
          const r = dfs(empty, 0, undefined);
          if(r === 'FOUND') return found;
          if(r === Infinity || nodes > nodeCap) break;
          threshold = r;
          if(Date.now() - t0 > tCap) break;
        }
        return null;
      }

      function bfsPlaceTile(currentState, fixedSet, targetVal, targetGoalIdx){
        const start = currentState.slice();
        const startEmpty = start.indexOf(null);
        const key = s => s.map(x=>x===null?'_':x).join(',');
        const Queue = [];
        const Seen = new Set();
        Queue.push({arr:start.slice(), empty:startEmpty, path:[]});
        Seen.add(key(start));
        const maxNodes = 200_000;
        let nodes=0;
        const maxDepth = 40;
        while(Queue.length){
          const node = Queue.shift();
          nodes++;
          if(nodes > maxNodes) break;
          if(node.arr[targetGoalIdx] === targetVal) return node.path.slice();
          if(node.path.length >= maxDepth) continue;
          const neigh = neighborsOfEmpty(node.empty);
          for(const idx of neigh){
            if(fixedSet.has(idx)) continue;
            const newA = node.arr.slice();
            newA[node.empty] = newA[idx];
            newA[idx] = null;
            const k = key(newA);
            if(Seen.has(k)) continue;
            Seen.add(k);
            const newPath = node.path.slice(); newPath.push(newA[node.empty]);
            Queue.push({arr:newA, empty: idx, path:newPath});
          }
        }
        return null;
      }

      function idaFull(initial, nodeCap=5_000_000, tCap=30_000){
        const state = initial.slice();
        let empty = state.indexOf(null);
        let nodes=0;
        function h(){ return manhattanUnfixed(state, new Set()); }
        let threshold = h();
        const path=[];
        let found=null;
        function dfs(eidx, g, prev){
          nodes++;
          if(nodes>nodeCap) return Infinity;
          const hv = manhattanUnfixed(state, new Set());
          const f = g + hv;
          if(f > threshold) return f;
          if(hv===0){ found = path.slice(); return 'FOUND'; }
          let min=Infinity;
          const neigh = neighborsOfEmpty(eidx);
          const order = neigh.map(idx=>{
            const val = state[idx];
            state[eidx]=val; state[idx]=null;
            const hv2 = manhattanUnfixed(state, new Set());
            state[idx]=val; state[eidx]=null;
            return {idx,hv2};
          }).sort((a,b)=>a.hv2-b.hv2);
          for(const o of order){
            const ti=o.idx;
            if(prev !== undefined && ti===prev) continue;
            const v = state[ti];
            state[eidx]=v; state[ti]=null;
            path.push(v);
            const r = dfs(ti, g+1, eidx);
            if(r==='FOUND') return 'FOUND';
            if(r < min) min = r;
            path.pop();
            state[ti]=v; state[eidx]=null;
          }
          return min;
        }
        const t0 = Date.now();
        while(true){
          nodes=0;
          const r = dfs(empty, 0, undefined);
          if(r==='FOUND') return found;
          if(r===Infinity || nodes>nodeCap) break;
          threshold = r;
          if(Date.now()-t0 > tCap) break;
        }
        return null;
      }

      if(size === 4){
        const working = startState.slice();
        let allMoves = [];
        const fixedIndices = new Set();
        try{
          for(let c=0; c<size; c++){
            const targetVal = c+1;
            const goalIdx = c;
            if(working[goalIdx]===targetVal){ fixedIndices.add(goalIdx); continue; }
            let moves = idaPlaceTarget(working, fixedIndices, targetVal, goalIdx, 300000, 4000);
            if(!moves) moves = bfsPlaceTile(working, fixedIndices, targetVal, goalIdx);
            if(!moves){ self.postMessage({type:'done', moves:null, method:'4x4_stage1_fail', tile:targetVal}); return; }
            for(const mv of moves){
              const fromIdx = working.indexOf(mv);
              const eIdx = working.indexOf(null);
              working[eIdx]=mv; working[fromIdx]=null;
              allMoves.push(mv);
            }
            if(working[goalIdx]!==targetVal){ self.postMessage({type:'done', moves:null, method:'4x4_not_placed', tile:targetVal}); return;}
            fixedIndices.add(goalIdx);
          }
          for(let i=4;i<=5;i++){
            const targetVal = i+1;
            const goalIdx = i;
            if(working[goalIdx]===targetVal){ fixedIndices.add(goalIdx); continue; }
            let moves = idaPlaceTarget(working, fixedIndices, targetVal, goalIdx, 200000, 3500);
            if(!moves) moves = bfsPlaceTile(working, fixedIndices, targetVal, goalIdx);
            if(!moves){ self.postMessage({type:'done', moves:null, method:'4x4_stage1_fail', tile:targetVal}); return; }
            for(const mv of moves){
              const fromIdx = working.indexOf(mv);
              const eIdx = working.indexOf(null);
              working[eIdx]=mv; working[fromIdx]=null;
              allMoves.push(mv);
            }
            if(working[goalIdx]!==targetVal){ self.postMessage({type:'done', moves:null, method:'4x4_not_placed', tile:targetVal}); return;}
            fixedIndices.add(goalIdx);
          }
          const restMoves = idaFull(working, 600000, 16000);
          if(restMoves&&restMoves.length>0){
            for(const mv of restMoves){
              const fromIdx = working.indexOf(mv);
              const eIdx = working.indexOf(null);
              working[eIdx]=mv; working[fromIdx]=null;
              allMoves.push(mv);
            }
            self.postMessage({type:'done', moves:allMoves, method:'4x4_stage2_ida'});
            return;
          }else{
            self.postMessage({type:'done', moves:allMoves.length?allMoves:null, method:'4x4_stage2_fail'});
            return;
          }
        }catch(e){
          self.postMessage({type:'done', moves:null, method:'4x4_exception', error:String(e)});
          return;
        }
      }
      if(size===5){
        const st1idx=[0,1,2,3,4,5,6,7,8,9,10,11];
        const working = startState.slice();
        let allMoves = [];
        const fixedIndices = new Set();
        try{
          for(const i of st1idx){
            const targetVal = i+1;
            const goalIdx = i;
            if(working[goalIdx]===targetVal){ fixedIndices.add(goalIdx); continue;}
            let moves = idaPlaceTarget(working, fixedIndices, targetVal, goalIdx, 170000, 3000);
            if(!moves) moves = bfsPlaceTile(working, fixedIndices, targetVal, goalIdx);
            if(!moves){ self.postMessage({type:'done', moves:null, method:'5x5_stage1_fail', tile:targetVal}); return; }
            for(const mv of moves){
              const fromIdx = working.indexOf(mv);
              const eIdx = working.indexOf(null);
              working[eIdx]=mv; working[fromIdx]=null;
              allMoves.push(mv);
            }
            if(working[goalIdx]!==targetVal){ self.postMessage({type:'done', moves:null, method:'5x5_not_placed', tile:targetVal}); return;}
            fixedIndices.add(goalIdx);
          }
          const restMoves = idaFull(working, 400000, 9000);
          if(restMoves&&restMoves.length>0){
            for(const mv of restMoves){
              const fromIdx = working.indexOf(mv);
              const eIdx = working.indexOf(null);
              working[eIdx]=mv; working[fromIdx]=null;
              allMoves.push(mv);
            }
            self.postMessage({type:'done', moves:allMoves, method:'5x5_stage2_ida'});
            return;
          }else{
            self.postMessage({type:'done', moves:allMoves.length?allMoves:null, method:'5x5_stage2_fail'});
            return;
          }
        }catch(e){
          self.postMessage({type:'done', moves:null, method:'5x5_exception', error:String(e)});
          return;
        }
      }
      if(size<=3){
        const moves = idaFull(startState);
        self.postMessage({type:'done', moves:moves, method:'3x3_ida'});
        return;
      }
      const fallback = idaFull(startState, 150000, 7000);
      self.postMessage({type:'done', moves:fallback, method:'fallback_ida'});
    }catch(e){
      self.postMessage({type:'done', moves:null, method:'worker_crash', error: String(e)});
    }
  };
}
const workerBlob = new Blob(['('+solverWorkerFunction.toString()+')()'], {type:'application/javascript'});
const workerUrl = URL.createObjectURL(workerBlob);
let solverWorker = null;
let solverRunning = false;
let queuedMoves = [];

function startSolver(onSolved, onFail, getTiles, getSize, isSolved, tryMove) {
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
  solverWorker.postMessage({type:'solve', state: snapshot, size});
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
