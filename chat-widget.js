/**
 * Ambore AI Chat Widget
 * Drop-in floating chat assistant for every page.
 * Calls /.netlify/functions/chat — no API key needed client-side.
 */
(function () {
  'use strict';

  const CHAT_API = '/.netlify/functions/chat';
  const WELCOME  = "Hi! I'm Ambore AI 👋 Ask me anything about the platform — jobs, resume builder, interview AI, or any other tool.";

  /* ── inject CSS ── */
  const style = document.createElement('style');
  style.textContent = `
  #amb-chat-btn{
    position:fixed;bottom:28px;right:28px;z-index:9998;
    width:56px;height:56px;border-radius:50%;
    background:linear-gradient(135deg,#6d5cff,#9c5fff);
    border:none;cursor:pointer;
    box-shadow:0 4px 24px rgba(109,92,255,0.5);
    display:flex;align-items:center;justify-content:center;
    transition:transform 0.2s,box-shadow 0.2s;
    color:#fff;
  }
  #amb-chat-btn:hover{transform:scale(1.08);box-shadow:0 6px 32px rgba(109,92,255,0.65)}
  #amb-chat-btn svg{width:24px;height:24px;transition:opacity 0.15s}
  #amb-chat-btn .ico-chat{opacity:1}
  #amb-chat-btn .ico-close{opacity:0;position:absolute}
  #amb-chat-btn.open .ico-chat{opacity:0}
  #amb-chat-btn.open .ico-close{opacity:1}

  /* unread badge */
  #amb-chat-badge{
    position:fixed;bottom:72px;right:28px;z-index:9999;
    background:#ef4444;color:#fff;border-radius:100px;
    font-size:0.7rem;font-weight:700;padding:3px 8px;
    display:none;pointer-events:none;
    box-shadow:0 2px 8px rgba(239,68,68,0.5);
  }

  #amb-chat-panel{
    position:fixed;bottom:96px;right:28px;z-index:9997;
    width:360px;max-width:calc(100vw - 40px);
    background:#0d0d1a;border:1px solid rgba(109,92,255,0.3);
    border-radius:20px;overflow:hidden;
    box-shadow:0 16px 64px rgba(0,0,0,0.6),0 0 0 1px rgba(109,92,255,0.1);
    display:flex;flex-direction:column;
    max-height:520px;
    transform:translateY(16px) scale(0.96);opacity:0;pointer-events:none;
    transition:transform 0.25s cubic-bezier(0.34,1.56,0.64,1),opacity 0.2s;
  }
  #amb-chat-panel.open{transform:translateY(0) scale(1);opacity:1;pointer-events:all}

  .amb-chat-head{
    display:flex;align-items:center;gap:10px;
    padding:14px 16px;
    background:rgba(109,92,255,0.12);
    border-bottom:1px solid rgba(109,92,255,0.2);
    flex-shrink:0;
  }
  .amb-chat-head-avatar{
    width:34px;height:34px;border-radius:50%;
    background:linear-gradient(135deg,#6d5cff,#9c5fff);
    display:flex;align-items:center;justify-content:center;
    font-size:1rem;font-weight:900;color:#fff;flex-shrink:0;
  }
  .amb-chat-head-info{flex:1;min-width:0}
  .amb-chat-head-name{font-size:0.88rem;font-weight:700;color:#fff;font-family:'Space Grotesk',sans-serif}
  .amb-chat-head-status{display:flex;align-items:center;gap:5px;font-size:0.72rem;color:rgba(255,255,255,0.45)}
  .amb-chat-head-dot{width:6px;height:6px;border-radius:50%;background:#22c55e;box-shadow:0 0 6px rgba(34,197,94,0.7);animation:ambPulse 2s infinite}
  @keyframes ambPulse{0%,100%{opacity:1}50%{opacity:0.5}}
  .amb-chat-head-close{background:none;border:none;color:rgba(255,255,255,0.3);cursor:pointer;padding:4px;line-height:1;font-size:1.1rem;transition:color 0.2s}
  .amb-chat-head-close:hover{color:#fff}

  .amb-chat-msgs{
    flex:1;overflow-y:auto;padding:16px;
    display:flex;flex-direction:column;gap:10px;
    scrollbar-width:thin;scrollbar-color:rgba(109,92,255,0.3) transparent;
  }
  .amb-msg{display:flex;gap:8px;align-items:flex-end;max-width:100%}
  .amb-msg.user{flex-direction:row-reverse}
  .amb-msg-bubble{
    padding:10px 13px;border-radius:14px;
    font-size:0.85rem;line-height:1.55;
    max-width:82%;word-break:break-word;
    font-family:'Space Grotesk',sans-serif;
  }
  .amb-msg.bot  .amb-msg-bubble{background:rgba(109,92,255,0.14);border:1px solid rgba(109,92,255,0.2);color:rgba(255,255,255,0.9);border-bottom-left-radius:4px}
  .amb-msg.user .amb-msg-bubble{background:linear-gradient(135deg,#6d5cff,#9c5fff);color:#fff;border-bottom-right-radius:4px}
  .amb-msg-avatar{width:26px;height:26px;border-radius:50%;flex-shrink:0;
    background:linear-gradient(135deg,#6d5cff,#9c5fff);
    display:flex;align-items:center;justify-content:center;font-size:0.7rem;font-weight:900;color:#fff}

  /* typing dots */
  .amb-typing{display:flex;align-items:center;gap:4px;padding:10px 13px;background:rgba(109,92,255,0.14);border:1px solid rgba(109,92,255,0.2);border-radius:14px;border-bottom-left-radius:4px;width:fit-content}
  .amb-typing span{width:6px;height:6px;border-radius:50%;background:rgba(109,92,255,0.7);animation:ambDot 1.2s infinite}
  .amb-typing span:nth-child(2){animation-delay:0.2s}
  .amb-typing span:nth-child(3){animation-delay:0.4s}
  @keyframes ambDot{0%,60%,100%{transform:translateY(0)}30%{transform:translateY(-5px)}}

  /* quick prompts */
  .amb-quick-chips{display:flex;flex-wrap:wrap;gap:6px;padding:0 16px 10px}
  .amb-chip{
    padding:5px 11px;border-radius:100px;
    background:rgba(109,92,255,0.08);border:1px solid rgba(109,92,255,0.22);
    font-size:0.75rem;font-weight:600;color:rgba(255,255,255,0.6);
    cursor:pointer;transition:all 0.2s;font-family:'Space Grotesk',sans-serif;white-space:nowrap;
  }
  .amb-chip:hover{background:rgba(109,92,255,0.2);color:#fff;border-color:rgba(109,92,255,0.5)}

  .amb-chat-footer{
    padding:10px 12px;border-top:1px solid rgba(109,92,255,0.15);
    display:flex;gap:8px;align-items:flex-end;flex-shrink:0;
  }
  #amb-chat-input{
    flex:1;resize:none;background:rgba(255,255,255,0.05);
    border:1px solid rgba(255,255,255,0.08);border-radius:10px;
    color:#fff;font-size:0.85rem;padding:9px 12px;outline:none;
    font-family:'Space Grotesk',sans-serif;line-height:1.4;
    max-height:100px;transition:border-color 0.2s;
  }
  #amb-chat-input:focus{border-color:rgba(109,92,255,0.5)}
  #amb-chat-input::placeholder{color:rgba(255,255,255,0.2)}
  #amb-chat-send{
    width:36px;height:36px;border-radius:10px;flex-shrink:0;
    background:linear-gradient(135deg,#6d5cff,#9c5fff);
    border:none;cursor:pointer;display:flex;align-items:center;justify-content:center;
    transition:opacity 0.2s,transform 0.1s;color:#fff;
  }
  #amb-chat-send:hover{opacity:0.85;transform:scale(1.05)}
  #amb-chat-send:disabled{opacity:0.3;cursor:default;transform:none}

  @media(max-width:400px){
    #amb-chat-panel{right:12px;bottom:84px;width:calc(100vw - 24px)}
    #amb-chat-btn{right:16px;bottom:20px}
    #amb-chat-badge{right:16px;bottom:66px}
  }
  `;
  document.head.appendChild(style);

  /* ── inject HTML ── */
  const wrap = document.createElement('div');
  wrap.innerHTML = `
  <span id="amb-chat-badge">1</span>

  <button id="amb-chat-btn" aria-label="Chat with Ambore AI">
    <!-- chat icon -->
    <svg class="ico-chat" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
      <path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/>
    </svg>
    <!-- close icon -->
    <svg class="ico-close" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round">
      <path d="M18 6L6 18M6 6l12 12"/>
    </svg>
  </button>

  <div id="amb-chat-panel" role="dialog" aria-label="Ambore AI Chat">
    <div class="amb-chat-head">
      <div class="amb-chat-head-avatar">A</div>
      <div class="amb-chat-head-info">
        <div class="amb-chat-head-name">Ambore AI</div>
        <div class="amb-chat-head-status"><span class="amb-chat-head-dot"></span>Online · Ready to help</div>
      </div>
      <button class="amb-chat-head-close" onclick="ambChat.close()" aria-label="Close chat">✕</button>
    </div>

    <div class="amb-chat-msgs" id="amb-chat-msgs"></div>

    <div class="amb-quick-chips" id="amb-quick-chips">
      <button class="amb-chip" onclick="ambChat.quick('How does the Interview AI work?')">Interview AI</button>
      <button class="amb-chip" onclick="ambChat.quick('How do I tailor my resume?')">Resume Builder</button>
      <button class="amb-chip" onclick="ambChat.quick('How many jobs are available?')">Job Portal</button>
      <button class="amb-chip" onclick="ambChat.quick('Is Ambore really free?')">Pricing</button>
    </div>

    <div class="amb-chat-footer">
      <textarea id="amb-chat-input" rows="1" placeholder="Ask anything about Ambore…" maxlength="500"></textarea>
      <button id="amb-chat-send" onclick="ambChat.send()" aria-label="Send">
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round">
          <line x1="22" y1="2" x2="11" y2="13"/><polygon points="22 2 15 22 11 13 2 9 22 2"/>
        </svg>
      </button>
    </div>
  </div>
  `;
  document.body.appendChild(wrap);

  /* ── state ── */
  const state = { open: false, history: [], typing: false, welcomed: false };

  /* ── DOM refs ── */
  const btn       = document.getElementById('amb-chat-btn');
  const panel     = document.getElementById('amb-chat-panel');
  const msgs      = document.getElementById('amb-chat-msgs');
  const input     = document.getElementById('amb-chat-input');
  const sendBtn   = document.getElementById('amb-chat-send');
  const badge     = document.getElementById('amb-chat-badge');
  const chips     = document.getElementById('amb-quick-chips');

  /* ── public API ── */
  window.ambChat = {
    toggle() { state.open ? this.close() : this.open(); },
    open() {
      state.open = true;
      btn.classList.add('open');
      panel.classList.add('open');
      badge.style.display = 'none';
      if (!state.welcomed) { addBotMsg(WELCOME); state.welcomed = true; }
      setTimeout(() => input.focus(), 250);
    },
    close() {
      state.open = false;
      btn.classList.remove('open');
      panel.classList.remove('open');
    },
    send() { sendMessage(input.value); },
    quick(text) {
      chips.style.display = 'none';
      sendMessage(text);
    },
  };

  btn.addEventListener('click', () => ambChat.toggle());

  /* auto-show badge after 4 seconds if not opened yet */
  setTimeout(() => {
    if (!state.welcomed) badge.style.display = 'block';
  }, 4000);

  /* ── keyboard ── */
  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      sendMessage(input.value);
    }
  });
  input.addEventListener('input', () => {
    input.style.height = 'auto';
    input.style.height = Math.min(input.scrollHeight, 100) + 'px';
  });

  /* ── core ── */
  function sendMessage(text) {
    text = (text || '').trim();
    if (!text || state.typing) return;
    chips.style.display = 'none';
    input.value = '';
    input.style.height = 'auto';
    addUserMsg(text);
    state.history.push({ role: 'user', content: text });
    showTyping();
    state.typing = true;
    sendBtn.disabled = true;

    fetch(CHAT_API, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ message: text, history: state.history.slice(0, -1) }),
    })
      .then(r => r.json())
      .then(data => {
        hideTyping();
        const reply = data.reply || data.error || 'Sorry, something went wrong. Please try again.';
        addBotMsg(reply);
        state.history.push({ role: 'assistant', content: reply });
      })
      .catch(() => {
        hideTyping();
        addBotMsg('Sorry, I\'m having trouble connecting. Please try again in a moment.');
      })
      .finally(() => {
        state.typing = false;
        sendBtn.disabled = false;
        input.focus();
      });
  }

  function addUserMsg(text) {
    const div = document.createElement('div');
    div.className = 'amb-msg user';
    div.innerHTML = `<div class="amb-msg-bubble">${escHtml(text)}</div>`;
    msgs.appendChild(div);
    scroll();
  }

  function addBotMsg(text) {
    const div = document.createElement('div');
    div.className = 'amb-msg bot';
    div.innerHTML = `
      <div class="amb-msg-avatar">A</div>
      <div class="amb-msg-bubble">${formatReply(text)}</div>`;
    msgs.appendChild(div);
    scroll();
  }

  let typingEl = null;
  function showTyping() {
    typingEl = document.createElement('div');
    typingEl.className = 'amb-msg bot';
    typingEl.innerHTML = `
      <div class="amb-msg-avatar">A</div>
      <div class="amb-typing"><span></span><span></span><span></span></div>`;
    msgs.appendChild(typingEl);
    scroll();
  }
  function hideTyping() {
    if (typingEl) { typingEl.remove(); typingEl = null; }
  }

  function scroll() { msgs.scrollTop = msgs.scrollHeight; }

  function escHtml(s) {
    return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
            .replace(/"/g,'&quot;').replace(/'/g,'&#39;');
  }

  function formatReply(text) {
    // Basic markdown: **bold**, line breaks
    return escHtml(text)
      .replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>')
      .replace(/\n/g, '<br>');
  }

})();
