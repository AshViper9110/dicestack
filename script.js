(() => {
  "use strict";

  const $ = (id) => document.getElementById(id);
  const ui = {
    menu: $("menuScreen"), game: $("gameScreen"), board: $("gameBoard"),
    create: $("createRoom"), joinForm: $("joinForm"), join: $("joinRoom"),
    peerInput: $("peerIdInput"), myPeerId: $("myPeerId"), hostPanel: $("hostPanel"),
    copy: $("copyId"), lobbyStatus: $("lobbyStatus"), waiting: $("waitingText"),
    connectionDot: $("connectionDot"), connectionText: $("connectionText"),
    connectionPill: document.querySelector(".connection-pill"),
    turnCard: $("turnCard"), turnPiece: $("turnPiece"), turnLabel: $("turnLabel"),
    turnHint: $("turnHint"), roundLabel: $("roundLabel"), whiteCard: $("whitePlayerCard"),
    blackCard: $("blackPlayerCard"), whiteRole: $("whiteRole"), blackRole: $("blackRole"),
    whiteState: $("whiteState"), blackState: $("blackState"), boardMessage: $("boardMessage"),
    result: $("resultBanner"), resultTitle: $("resultTitle"), resultDescription: $("resultDescription"),
    resultIcon: $("resultIcon"), rematch: $("rematchButton"), back: $("backToMenu"),
    matchId: $("matchIdLabel"), dialog: $("rulesDialog"), toast: $("toast")
  };

  const COLS = 5, ROWS = 7;
  const COLORS = { WHITE: "white", BLACK: "black" };
  let peer = null, conn = null, role = null, myColor = null;
  let roomCode = null;
  let game = null, selectedDieId = null, legalTargets = [];
  let roomOpen = false, opponentReady = false, connectionLost = false;
  let toastTimer = null, listenerEpoch = 0, localMatchCounter = 0;
  let rematchVotes = new Set();

  function clone(value) { return JSON.parse(JSON.stringify(value)); }
  function coordKey(x, y) { return `${x},${y}`; }
  function inBounds(x, y) { return Number.isInteger(x) && Number.isInteger(y) && x >= 0 && x < COLS && y >= 0 && y < ROWS; }
  function nextValue(n) { return n === 3 ? 1 : n + 1; }

  // Game logic is intentionally independent of DOM rendering and transport.
  const Rules = {
    initialState() {
      const dice = [];
      [["B1","BLACK",1,0],["C1","BLACK",2,0],["D1","BLACK",3,0],
       ["B7","WHITE",1,6],["C7","WHITE",2,6],["D7","WHITE",3,6]]
        .forEach(([id,color,x,y]) => dice.push({ id, color, x, y, value: 1, stackOrder: 0 }));
      return { version: 1, dice, turn: "WHITE", status: "playing", winner: null,
        winReason: null, turnNumber: 1, lastMove: null, matchId: `DS-${Date.now().toString(36).toUpperCase()}` };
    },
    stackAt(state, x, y) {
      return state.dice.filter(d => d.x === x && d.y === y)
        .sort((a, b) => (a.stackOrder || 0) - (b.stackOrder || 0));
    },
    reachedGoal(state, color) {
      // Goal squares are the two outer corners on the opponent's starting row:
      // A1/E1 for White, A7/E7 for Black.
      const enemyHomeY = color === "WHITE" ? 0 : ROWS - 1;
      return state.dice.some(d => d.color === color && d.y === enemyHomeY && (d.x === 0 || d.x === COLS - 1));
    },
    allOpponentsStacked(state, color) {
      const enemyColor = color === "WHITE" ? "BLACK" : "WHITE";
      const enemies = state.dice.filter(d => d.color === enemyColor);
      return enemies.length > 0 && enemies.every(enemy => {
        const stack = this.stackAt(state, enemy.x, enemy.y);
        const index = stack.findIndex(d => d.id === enemy.id);
        return index >= 0 && index < stack.length - 1 && stack[index + 1].color === color;
      });
    },
    topAt(state, x, y) {
      const stack = this.stackAt(state, x, y);
      return stack.length ? stack[stack.length - 1] : null;
    },
    topForDie(state, die) {
      const stack = this.stackAt(state, die.x, die.y);
      return stack.length ? stack[stack.length - 1].id === die.id : false;
    },
    getDie(state, id) { return state.dice.find(d => d.id === id) || null; },
    legalMove(state, dieId, x, y, color) {
      if (!state || state.status !== "playing") return { ok:false, reason:"対局は終了しています。" };
      if (state.turn !== color) return { ok:false, reason:"相手の手番です。" };
      const die = this.getDie(state, dieId);
      if (!die) return { ok:false, reason:"存在しないダイスです。" };
      if (die.color !== color) return { ok:false, reason:"相手のダイスは操作できません。" };
      if (!this.topForDie(state, die)) return { ok:false, reason:"下に押さえ込まれたダイスは動かせません。" };
      if (!inBounds(x,y)) return { ok:false, reason:"盤面の外へは移動できません。" };
      const dx = Math.abs(x-die.x), dy = Math.abs(y-die.y);
      if ((dx === 0 && dy === 0) || dx > 1 || dy > 1) return { ok:false, reason:"1マス先の8方向だけ移動できます。" };
      const target = this.topAt(state,x,y);
      if (target && target.color === color) return { ok:false, reason:"自分のダイスがあるマスには移動できません。" };
      const newValue = nextValue(die.value);
      if (target && newValue <= target.value) return { ok:false, reason:`移動後の数字 ${newValue} は相手の数字 ${target.value} 以下です。` };
      return { ok:true, die, target, newValue };
    },
    move(state, dieId, x, y, color) {
      const check = this.legalMove(state,dieId,x,y,color);
      if (!check.ok) return check;
      const next = clone(state);
      const die = next.dice.find(d => d.id === dieId);
      const from = {x:die.x,y:die.y};
      die.x = x; die.y = y; die.value = check.newValue;
      // A moved die becomes the top die on the destination stack. If it leaves
      // a stack, the remaining die(s) retain their relative order.
      const destinationStack = this.stackAt(next, x, y).filter(d => d.id !== dieId);
      die.stackOrder = destinationStack.length
        ? Math.max(...destinationStack.map(d => d.stackOrder || 0)) + 1
        : 0;
      next.turnNumber += 1;
      next.turn = color === "WHITE" ? "BLACK" : "WHITE";
      next.lastMove = { dieId, color, from, to:{x,y}, value:die.value, stacked:!!check.target };
      if (this.reachedGoal(next, color)) {
        next.status = "finished"; next.winner = color; next.winReason = "goal";
      } else if (this.allOpponentsStacked(next, color)) {
        next.status = "finished"; next.winner = color; next.winReason = "all-stacked";
      }
      return {ok:true,state:next};
    },
    validateState(state) {
      if (!state || state.version !== 1 || !Array.isArray(state.dice) || state.dice.length !== 6) return false;
      if (!["WHITE","BLACK"].includes(state.turn) || !["playing","finished"].includes(state.status)) return false;
      if (!Number.isInteger(state.turnNumber) || state.turnNumber < 1) return false;
      const ids = new Set();
      for (const d of state.dice) {
        if (!d || typeof d.id !== "string" || ids.has(d.id) ||
            !["WHITE","BLACK"].includes(d.color) || !inBounds(d.x,d.y) ||
            !Number.isInteger(d.value) || d.value < 1 || d.value > 3 ||
            (d.stackOrder !== undefined && (!Number.isInteger(d.stackOrder) || d.stackOrder < 0))) return false;
        ids.add(d.id);
      }
      if (state.status === "finished" && !["WHITE","BLACK"].includes(state.winner)) return false;
      if (state.status === "playing" && state.winner !== null) return false;
      return true;
    },
    movesFor(state, dieId, color) {
      const die = this.getDie(state,dieId);
      if (!die || die.color !== color || !this.topForDie(state,die) || state.turn !== color || state.status !== "playing") return [];
      const moves = [];
      for (let dy=-1;dy<=1;dy++) for(let dx=-1;dx<=1;dx++) {
        if (!dx && !dy) continue;
        const x=die.x+dx,y=die.y+dy;
        if (this.legalMove(state,dieId,x,y,color).ok) moves.push({x,y});
      }
      return moves;
    }
  };

  function setConnection(text, state="") {
    ui.connectionText.textContent = text;
    ui.connectionPill.classList.toggle("connected", state === "connected");
    ui.connectionPill.classList.toggle("error", state === "error");
    ui.connectionPill.setAttribute("aria-label", `接続状態: ${text}`);
  }
  function setLobbyStatus(text, error=false) {
    ui.lobbyStatus.textContent = text;
    ui.lobbyStatus.classList.toggle("error",error);
  }
  function toast(text) {
    ui.toast.textContent=text; ui.toast.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer=setTimeout(()=>ui.toast.classList.remove("show"),2400);
  }
  function showGame() {
    ui.menu.classList.add("hidden"); ui.game.classList.remove("hidden");
    window.scrollTo({top:0,behavior:"smooth"});
  }
  function showMenu() {
    ui.game.classList.add("hidden"); ui.menu.classList.remove("hidden");
    window.scrollTo({top:0,behavior:"smooth"});
  }
  function showRules() {
    if (typeof ui.dialog.showModal === "function") ui.dialog.showModal();
    else alert("ルールはHTML内のルール欄を確認してください。");
  }
  function setBusy(busy) {
    ui.create.disabled=busy; ui.join.disabled=busy;
    ui.create.style.opacity=busy?".65":"1"; ui.join.style.opacity=busy?".65":"1";
  }
  function generateRoomCode() {
    // The four-digit code is also the PeerJS ID. No local lookup table is needed.
    // If another active room already owns the code, PeerJS reports unavailable-id.
    return String(Math.floor(Math.random() * 10000)).padStart(4, "0");
  }
  function peerAvailable() {
    if (window.__peerScriptFailed || typeof window.Peer !== "function") {
      setLobbyStatus("PeerJSを読み込めませんでした。CDN接続や広告ブロッカーを確認して再読み込みしてください。",true);
      setConnection("PeerJS読み込みエラー","error");
      return false;
    }
    return true;
  }
  function disposePeer() {
    listenerEpoch++;
    try { if (conn) { conn.removeAllListeners(); conn.close(); } } catch (_) {}
    try { if (peer) { peer.removeAllListeners(); peer.destroy(); } } catch (_) {}
    peer=null; conn=null; roomOpen=false; opponentReady=false; connectionLost=false;
  }
  function createPeer(requestedId = null) {
    if (!peerAvailable()) return null;
    disposePeer();
    // The four-digit room code is the PeerJS ID itself, so another browser can
    // connect using only that code without a backend or shared local directory.
    peer = new Peer(requestedId || undefined, { debug: 1, config: { iceServers: [
      { urls: "stun:stun.l.google.com:19302" }
    ]}});
    const epoch=listenerEpoch;
    peer.on("open", id => {
      if (epoch !== listenerEpoch) return;
      roomCode = id;
      ui.myPeerId.value=id;
      ui.hostPanel.classList.remove("hidden");
      setLobbyStatus("部屋を作成しました。4桁のルームIDを相手に共有してください。");
      setConnection("相手を待っています");
      setBusy(false);
    });
    peer.on("connection", incoming => {
      if (epoch !== listenerEpoch) { incoming.close(); return; }
      if (role !== "host" || conn || opponentReady) {
        incoming.on("open",()=>incoming.send({type:"ERROR",message:"この部屋はすでに満員です。"}));
        setTimeout(()=>incoming.close(),500);
        return;
      }
      conn=incoming;
      setupConnection(conn,epoch);
    });
    peer.on("error", err => {
      if(epoch!==listenerEpoch) return;
      console.error("PeerJS error:",err.type || err);
      const message = err.type==="peer-unavailable" ? "そのルームIDの接続先が見つかりません。IDを確認してください。" :
        err.type==="unavailable-id" ? "IDを確保できませんでした。もう一度お試しください。" :
        "PeerJS接続エラーです。ネットワークやPeerJSサーバーの状態を確認してください。";
      setLobbyStatus(message,true); setConnection("接続エラー","error"); setBusy(false);
      if(role==="guest" && !conn) toast(message);
    });
    peer.on("disconnected",()=>{
      if(epoch!==listenerEpoch) return;
      setConnection("シグナリング切断","error");
      if(role==="host" && !conn) setLobbyStatus("PeerJSシグナリングサーバーから切断されました。再読み込みしてください。",true);
    });
    return peer;
  }
  function setupConnection(connection, epoch) {
    connection.on("open",()=>{
      if(epoch!==listenerEpoch || connection!==conn) return;
      opponentReady=true; connectionLost=false;
      setConnection("対戦相手と接続中","connected");
      if(role==="host") {
        // One guest only. Send full authoritative state after the connection opens.
        game=Rules.initialState(); selectedDieId=null; legalTargets=[];
        send({type:"GAME_START",state:game,hostColor:"WHITE",guestColor:"BLACK"});
        render();
        setLobbyStatus("相手が接続しました。対局を開始します。");
        showGame();
      } else {
        send({type:"JOIN_ROOM",protocol:1});
        setLobbyStatus("ホストから初期盤面を待っています。");
      }
    });
    connection.on("data",raw=>{
      if(epoch!==listenerEpoch || connection!==conn) return;
      handleMessage(raw);
    });
    connection.on("close",()=>{
      if(epoch!==listenerEpoch) return;
      opponentReady=false; connectionLost=true;
      setConnection("相手との接続が切れました","error");
      if(role==="host") {
        if(game && game.status==="playing") ui.boardMessage.textContent="相手が切断しました。対局は一時停止中です。";
        ui.waiting.textContent="相手との接続が切れました。メニューへ戻って部屋を作り直してください。";
        toast("相手との接続が切れました。");
      } else {
        if(game && game.status==="playing") ui.boardMessage.textContent="ホストが切断しました。対局を終了してください。";
        toast("ホストとの接続が切れました。メニューへ戻ってください。");
      }
      render();
    });
    connection.on("error",err=>{
      if(epoch!==listenerEpoch) return;
      console.error("DataConnection error:",err);
      connectionLost=true; setConnection("通信エラー","error");
      ui.boardMessage.textContent="通信エラーにより対局を一時停止しています。";
      render();
    });
  }
  function send(message) {
    if(!conn || !conn.open) return false;
    try { conn.send(message); return true; }
    catch(err) { console.error("Send failed:",err); setConnection("送信エラー","error"); return false; }
  }
  function validMessage(raw) {
    if(!raw || typeof raw!=="object" || Array.isArray(raw) || typeof raw.type!=="string") return false;
    if(raw.type.length>40) return false;
    return true;
  }
  function handleMessage(raw) {
    if(!validMessage(raw)) { send({type:"ERROR",message:"不正な通信メッセージです。"}); return; }
    switch(raw.type) {
      case "JOIN_ROOM":
        if(role!=="host" || !conn || !conn.open || !opponentReady) {
          send({type:"ERROR",message:"この部屋には参加できません。"}); return;
        }
        // GAME_START is sent when the data connection opens. JOIN_ROOM is an
        // additional handshake and must not reset or reject that already-started match.
        roomOpen=true;
        if(!game) game=Rules.initialState();
        send({type:"GAME_START",state:game,hostColor:"WHITE",guestColor:"BLACK"});
        break;
      case "GAME_START":
        if(role!=="guest" || !Rules.validateState(raw.state) ||
           raw.hostColor!=="WHITE" || raw.guestColor!=="BLACK") {
          toast("ホストから不正な初期状態を受信しました。"); return;
        }
        game=clone(raw.state); myColor="BLACK"; selectedDieId=null; legalTargets=[];
        showGame(); render(); setLobbyStatus("ホストと接続しました。あなたは黒です。");
        setConnection("対戦相手と接続中","connected");
        break;
      case "MOVE_REQUEST":
        if(role!=="host") return;
        if(!game || !conn || !conn.open || !opponentReady) return;
        if(raw.color!=="BLACK" || typeof raw.dieId!=="string" || !Number.isInteger(raw.x) || !Number.isInteger(raw.y)) {
          send({type:"ERROR",message:"移動要求の形式が不正です。"}); return;
        }
        applyAuthoritativeMove(raw.dieId,raw.x,raw.y,"BLACK");
        break;
      case "STATE_UPDATE":
        if(role!=="guest" || !Rules.validateState(raw.state)) { send({type:"ERROR",message:"不正なゲーム状態です。"}); return; }
        game=clone(raw.state); selectedDieId=null; legalTargets=[];
        render();
        if(game.status==="finished") send({type:"GAME_END_ACK",turnNumber:game.turnNumber});
        break;
      case "GAME_END":
        if(role==="guest" && Rules.validateState(raw.state)) { game=clone(raw.state); render(); }
        break;
      case "REMATCH_REQUEST":
        if(role==="host") {
          if(raw.accept===true) rematchVotes.add("BLACK");
          else { rematchVotes.delete("BLACK"); toast("相手が再戦をキャンセルしました。"); return; }
          if(rematchVotes.has("WHITE")) startRematch();
          else toast("相手が再戦に同意しました。再戦ボタンを押してください。");
        } else if(role==="guest") {
          // A request is not an automatic vote for both players. The guest must
          // press the rematch button to consent; the host then broadcasts the reset.
          toast("ホストが再戦を希望しています。再戦ボタンを押して同意してください。");
        }
        break;
      case "ERROR":
        toast(typeof raw.message==="string" ? raw.message.slice(0,180) : "通信エラーが発生しました。");
        break;
      case "GAME_END_ACK": break;
      default:
        send({type:"ERROR",message:"未対応のメッセージ種別です。"});
    }
  }
  function applyAuthoritativeMove(dieId,x,y,color) {
    if(!game || game.status!=="playing") { send({type:"ERROR",message:"対局終了後は移動できません。"}); return; }
    if(game.turn!==color) { send({type:"ERROR",message:"手番違反です。"}); return; }
    const result=Rules.move(game,dieId,x,y,color);
    if(!result.ok) { send({type:"ERROR",message:result.reason}); return; }
    game=result.state; selectedDieId=null; legalTargets=[];
    send({type:game.status==="finished"?"GAME_END":"STATE_UPDATE",state:game});
    render();
  }
  function startRematch() {
    if(role!=="host") return;
    game=Rules.initialState(); game.matchId=`DS-${Date.now().toString(36).toUpperCase()}`;
    selectedDieId=null; legalTargets=[]; rematchVotes.clear();
    send({type:"STATE_UPDATE",state:game});
    render(); toast("新しい対局を開始しました。");
  }
  function selectDie(die) {
    if(!game || game.status!=="playing" || connectionLost || !opponentReady) return;
    if(die.color!==myColor || game.turn!==myColor) { toast("自分の手番ではありません。"); return; }
    if(!Rules.topForDie(game,die)) { toast("下に押さえ込まれたダイスは動かせません。"); return; }
    selectedDieId=die.id;
    legalTargets=Rules.movesFor(game,die.id,myColor);
    render();
  }
  function onCellClick(x,y) {
    if(!game || game.status!=="playing" || connectionLost || !opponentReady) return;
    const top=Rules.topAt(game,x,y);
    if(selectedDieId) {
      const isLegal=legalTargets.some(p=>p.x===x&&p.y===y);
      if(isLegal) {
        if(role==="host") applyAuthoritativeMove(selectedDieId,x,y,myColor);
        else {
          send({type:"MOVE_REQUEST",dieId:selectedDieId,x,y,color:myColor});
          selectedDieId=null; legalTargets=[]; ui.boardMessage.textContent="移動要求をホストに送信しました…";
          render();
        }
        return;
      }
      if(top && top.color===myColor) { selectDie(top); return; }
      toast("そのマスには移動できません。"); return;
    }
    if(top) selectDie(top);
  }
  function render() {
    if(!game) return;
    // Keep the opponent represented first (upper/sidebar top) and self second.
    const whiteIsSelf = myColor === "WHITE";
    ui.whiteRole.textContent = whiteIsSelf ? "自分 · ホスト" : "相手 · ホスト";
    ui.blackRole.textContent = whiteIsSelf ? "相手 · ゲスト" : "自分 · ゲスト";
    ui.whiteCard.style.order = whiteIsSelf ? "2" : "1";
    ui.blackCard.style.order = whiteIsSelf ? "1" : "2";
    renderBoard();
    const yourTurn=game.status==="playing" && game.turn===myColor && !connectionLost && opponentReady;
    const isWhiteTurn=game.turn==="WHITE";
    ui.turnPiece.textContent=isWhiteTurn?"W":"B";
    ui.turnPiece.className=`player-token ${isWhiteTurn?"white-token":"black-token"}`;
    ui.turnLabel.textContent=isWhiteTurn?"白のターン":"黒のターン";
    ui.roundLabel.textContent=`TURN ${String(game.turnNumber).padStart(2,"0")}`;
    ui.turnCard.classList.toggle("active",yourTurn);
    ui.whiteCard.classList.toggle("active",game.turn==="WHITE"&&game.status==="playing");
    ui.blackCard.classList.toggle("active",game.turn==="BLACK"&&game.status==="playing");
    if(connectionLost) ui.turnHint.textContent="通信切断中。接続が復旧するまで操作できません。";
    else if(game.status==="finished") ui.turnHint.textContent="対局終了。再戦する場合は両者が同意してください。";
    else if(yourTurn) ui.turnHint.textContent=selectedDieId?"移動先のマスを選択してください。":"操作するダイスを選択してください。";
    else ui.turnHint.textContent="相手の手番です。次の一手を考えましょう。";
    ui.boardMessage.textContent=game.status==="finished"?"対局終了":yourTurn?"あなたの手番です":`${isWhiteTurn?"白":"黒"}の手番です`;
    ui.matchId.textContent=`MATCH ${game.matchId || "—"}`;
    ui.rematch.classList.toggle("hidden",game.status!=="finished");
    if(game.status==="finished") {
      ui.result.classList.remove("hidden");
      const winner=game.winner==="WHITE"?"白（WHITE）":"黒（BLACK）";
      ui.resultTitle.textContent=`${game.winner==="WHITE"?"WHITE":"BLACK"} WINS`;
      ui.resultDescription.textContent=game.winReason==="goal"
        ? `${winner}が相手陣地のゴールマスに到達しました。`
        : `${winner}が相手のダイス3個すべてにスタックしました。`;
      ui.resultIcon.textContent="▰";
    } else ui.result.classList.add("hidden");
  }
  function renderBoard() {
    ui.board.replaceChildren();
    const rowLabels = document.querySelector(".row-labels");
    if (rowLabels) {
      rowLabels.replaceChildren();
      for (let displayY=0; displayY<ROWS; displayY++) {
        const label=document.createElement("span");
        label.textContent=String((myColor==="BLACK" ? ROWS-1-displayY : displayY)+1);
        rowLabels.append(label);
      }
    }
    for(let displayY=0;displayY<ROWS;displayY++) for(let x=0;x<COLS;x++) {
      const y = myColor === "BLACK" ? ROWS - 1 - displayY : displayY;
      const cell=document.createElement("button");
      cell.type="button"; cell.className="board-cell";
      cell.setAttribute("role","gridcell");
      cell.setAttribute("aria-label",`${"ABCDE"[x]}${y+1}`);
      cell.dataset.x=x; cell.dataset.y=y;
      const enemyHomeY = myColor === "BLACK" ? ROWS - 1 : 0;
      if(y===enemyHomeY&&(x===0||x===COLS-1)) cell.classList.add("goal-cell");
      const coord=document.createElement("span"); coord.className="coord"; coord.textContent=`${"ABCDE"[x]}${y+1}`; cell.append(coord);
      const stack=Rules.stackAt(game,x,y);
      const legal=legalTargets.some(p=>p.x===x&&p.y===y);
      if(legal) {
        cell.classList.add("legal");
        if(stack.length) cell.classList.add("stack-legal");
      }
      if(selectedDieId && stack.some(d=>d.id===selectedDieId)) cell.classList.add("selected");
      if(stack.length) {
        const stackEl=document.createElement("div"); stackEl.className=`die-stack stack-${Math.min(stack.length,3)}`;
        stack.forEach((die,index)=>{
          const dieEl=document.createElement("div");
          dieEl.className=`die ${die.color.toLowerCase()} owner-${die.color.toLowerCase()}${index===stack.length-1?" top-die":""}`;
          dieEl.textContent=String(die.value);
          dieEl.style.zIndex=String(index+1);
          if(index!==stack.length-1) {
            dieEl.style.position="absolute";
            dieEl.style.transform=`translateY(${(index-(stack.length-1))*5}px) scale(${1-(stack.length-1-index)*.04})`;
          }
          dieEl.setAttribute("aria-label",`${die.color==="WHITE"?"白":"黒"}のダイス、数字${die.value}${index===stack.length-1?"、最上段":""}`);
          stackEl.append(dieEl);
        });
        cell.append(stackEl);
      }
      cell.disabled=game.status!=="playing" || connectionLost || !opponentReady;
      cell.addEventListener("click",()=>onCellClick(x,y));
      ui.board.append(cell);
    }
  }

  ui.create.addEventListener("click",()=>{
    if(peer || conn) disposePeer();
    role="host"; myColor="WHITE"; game=null; selectedDieId=null; legalTargets=[];
    ui.hostPanel.classList.remove("hidden"); ui.myPeerId.value=""; ui.waiting.textContent="相手がこのIDを入力するまで待機中です。";
    setBusy(true); setConnection("部屋を作成中"); setLobbyStatus("PeerJSに接続しています…");
    const p=createPeer(generateRoomCode());
    if(!p) {setBusy(false);return;}
    ui.create.disabled=true;
  });
  ui.joinForm.addEventListener("submit",event=>{
    event.preventDefault();
    const code=ui.peerInput.value.trim();
    if(!/^\d{4}$/.test(code)) {setLobbyStatus("4桁の数字のルームIDを入力してください。",true);return;}
    const target=code;
    if(peer || conn) disposePeer();
    role="guest"; myColor="BLACK"; game=null; selectedDieId=null; legalTargets=[];
    setBusy(true); setConnection("ホストへ接続中"); setLobbyStatus("PeerJSに接続しています…");
    const p=createPeer();
    if(!p) {setBusy(false);return;}
    p.on("open",()=>{
      if(role!=="guest" || !peer) return;
      const epoch=listenerEpoch;
      conn=peer.connect(target,{reliable:true,serialization:"json",metadata:{game:"DICE_STACK",protocol:1}});
      setupConnection(conn,epoch);
      conn.on("open",()=>{ setLobbyStatus("ホストへ接続しました。応答を待っています…"); });
      setTimeout(()=>{
        if(role==="guest" && (!conn || !conn.open)) {
          setLobbyStatus("接続がタイムアウトしました。Peer IDとネットワークを確認してください。",true);
          setBusy(false);
        }
      },15000);
    });
  });
  ui.copy.addEventListener("click",async()=>{
    const id=ui.myPeerId.value;
    if(!id) return;
    try { await navigator.clipboard.writeText(id); toast("Peer IDをコピーしました。"); }
    catch(_) { ui.myPeerId.select(); try {document.execCommand("copy");toast("Peer IDをコピーしました。");} catch(__) {toast("IDを選択して手動でコピーしてください。");} }
  });
  ui.back.addEventListener("click",()=>{
    disposePeer(); role=null; myColor=null; game=null; selectedDieId=null; legalTargets=[];
    roomCode=null;
    ui.hostPanel.classList.add("hidden"); ui.myPeerId.value=""; ui.peerInput.value="";
    setConnection("オフライン"); setLobbyStatus("オンライン対戦にはインターネット接続が必要です。");
    setBusy(false); showMenu();
  });
  ui.rematch.addEventListener("click",()=>{
    if(!game || game.status!=="finished" || connectionLost) return;
    if(role==="host") {
      rematchVotes.add("WHITE");
      send({type:"REMATCH_REQUEST",accept:true});
      if(rematchVotes.has("BLACK")) startRematch();
      else toast("再戦を申し込みました。相手の同意を待っています。");
    } else {
      send({type:"REMATCH_REQUEST",accept:true});
      toast("再戦に同意しました。");
    }
  });
  $("rulesOpen").addEventListener("click",showRules);
  $("rulesOpenGame").addEventListener("click",showRules);
  $("rulesClose").addEventListener("click",()=>ui.dialog.close());
  ui.dialog.addEventListener("click",e=>{if(e.target===ui.dialog)ui.dialog.close();});

  // Browser-console regression suite: run DiceStack.runTests() after the page loads.
  function runTests() {
    const results = [];
    const test = (name, fn) => {
      try { if (fn() !== true) throw new Error("assertion failed"); results.push({name, pass:true}); }
      catch (error) { results.push({name, pass:false, error:String(error.message || error)}); }
    };
    const fresh = () => Rules.initialState();
    const move = (state, id, x, y, color) => Rules.move(state,id,x,y,color);
    const assert = (condition) => { if (!condition) throw new Error("assertion failed"); return true; };
    const isolated = (color="WHITE", x=2, y=3, value=1) => {
      const state=fresh();
      state.dice.forEach(d=>{d.x=0;d.y=0;});
      const die=state.dice.find(d=>d.color===color);
      die.x=x;die.y=y;die.value=value;
      // Park the other dice together on the far bottom-left square so test targets stay clear.
      state.dice.filter(d=>d.id!==die.id).forEach(d=>{d.x=0;d.y=6;});
      state.turn=color; state.status="playing"; state.winner=null; state.winReason=null;
      return state;
    };
    test("初期配置：白B7/C7/D7、黒B1/C1/D1、全て数字1",()=>{
      const s=fresh(), pos=s.dice.map(d=>`${d.color}:${"ABCDE"[d.x]}${d.y+1}:${d.value}`).sort();
      return assert(pos.join("|")==="BLACK:B1:1|BLACK:C1:1|BLACK:D1:1|WHITE:B7:1|WHITE:C7:1|WHITE:D7:1");
    });
    test("数字の循環 1→2→3→1",()=>assert(nextValue(1)===2&&nextValue(2)===3&&nextValue(3)===1));
    test("8方向への1マス移動",()=>{
      const dirs=[[-1,-1],[0,-1],[1,-1],[-1,0],[1,0],[-1,1],[0,1],[1,1]];
      return assert(dirs.every(([dx,dy])=>Rules.legalMove(isolated(), "B7",2+dx,3+dy,"WHITE").ok));
    });
    test("盤面外への移動拒否",()=>assert(!Rules.legalMove(isolated(),"B7",5,3,"WHITE").ok));
    test("自分のダイスがあるマスへの移動拒否",()=>{
      const s=isolated(); const d=s.dice.find(d=>d.id==="C7"); d.x=3;d.y=3;
      return assert(!Rules.legalMove(s,"B7",3,3,"WHITE").ok);
    });
    test("下に押さえ込まれたダイスは移動不可",()=>{
      const s=fresh(); const lower=s.dice.find(d=>d.id==="C1"); const upper={...lower,id:"TEST_TOP",color:"WHITE",value:2};
      s.dice.push(upper); s.turn="BLACK";
      return assert(!Rules.legalMove(s,lower.id,1,1,"BLACK").ok);
    });
    test("移動後の数字でスタック判定（1→2なら相手1に成功するが即勝利ではない）",()=>{
      const s=isolated(); const target=s.dice.find(d=>d.id==="B1"); target.x=3;target.y=3;target.value=1;
      const r=move(s,"B7",3,3,"WHITE");
      return assert(r.ok&&r.state.dice.find(d=>d.id==="B7").value===2&&r.state.status==="playing");
    });
    test("移動後の数字が相手以下ならスタック拒否（3→1対1）",()=>{
      const s=isolated("WHITE",2,3,3); const target=s.dice.find(d=>d.id==="B1"); target.x=3;target.y=3;target.value=1;
      return assert(!move(s,"B7",3,3,"WHITE").ok);
    });
    test("相手陣のゴールマスA1到達で白が勝利",()=>{
      const s=isolated("WHITE",1,1,1); const r=move(s,"B7",0,0,"WHITE");
      return assert(r.ok&&r.state.status==="finished"&&r.state.winner==="WHITE"&&r.state.winReason==="goal");
    });
    test("相手陣のゴール以外のマスでは勝利しない",()=>{
      const s=isolated("WHITE",2,1,1); const r=move(s,"B7",2,0,"WHITE");
      return assert(r.ok&&r.state.status==="playing"&&r.state.winner===null);
    });
    test("黒はA7/E7がゴール",()=>{
      const s=isolated("BLACK",1,5,1); s.turn="BLACK";
      s.dice.filter(d=>d.id!=="B1").forEach(d=>{d.x=2;d.y=3;});
      const r=move(s,"B1",0,6,"BLACK");
      return assert(r.ok&&r.state.status==="finished"&&r.state.winner==="BLACK"&&r.state.winReason==="goal");
    });
    test("相手のダイス3個すべてを覆うと勝利",()=>{
      const s=fresh();
      // Place all three opposing dice under one friendly die each.
      const whites=s.dice.filter(d=>d.color==="WHITE");
      const blacks=s.dice.filter(d=>d.color==="BLACK");
      for(let i=0;i<3;i++){
        whites[i].x=i; whites[i].y=3; whites[i].stackOrder=1;
        blacks[i].x=i; blacks[i].y=3; blacks[i].stackOrder=0;
      }
      s.turn="WHITE";
      return assert(Rules.allOpponentsStacked(s,"WHITE"));
    });
    test("勝利後の操作拒否",()=>{
      const s=fresh(); s.status="finished";s.winner="WHITE";s.winReason="goal";
      return assert(!Rules.move(s,"B7",1,5,"WHITE").ok);
    });
    test("手番違反の拒否",()=>assert(!Rules.move(fresh(),"B1",1,1,"BLACK").ok));
    test("状態のシリアライズ往復でホスト・ゲスト状態が一致",()=>{
      const s=fresh(), guestCopy=JSON.parse(JSON.stringify(s));
      return assert(Rules.validateState(guestCopy)&&JSON.stringify(s)===JSON.stringify(guestCopy));
    });
    const failed=results.filter(r=>!r.pass);
    return {passed:results.length-failed.length,total:results.length,failed,results};
  }
  window.DiceStack = { Rules, getState:()=>game?clone(game):null, getRole:()=>role, runTests };
  setConnection("オフライン");
  if(window.__peerScriptFailed || typeof window.Peer!=="function") {
    // defer may not have loaded yet; user gets a clear error only when trying to connect.
    setLobbyStatus("PeerJSはオンライン対戦開始時に確認されます。");
  }
})();