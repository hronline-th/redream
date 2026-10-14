/*
 * HR onLine – PDF lock (AES-256, PDF 2.0 standard security, R6)
 * Locks an existing PDF with a password, on the phone, before saving.
 * Needs pdf-lib (PDFLib global) and WebCrypto (any modern browser on https).
 * Usage: const bytes = await PdfLock.lock(pdfBytes, '19980324');
 */
(function (root) {
  'use strict';
  const subtle = (root.crypto || globalThis.crypto || {}).subtle;
  const rand = n => (root.crypto || globalThis.crypto).getRandomValues(new Uint8Array(n));

  function cat() {
    let len = 0;
    for (const a of arguments) len += a.length;
    const out = new Uint8Array(len);
    let o = 0;
    for (const a of arguments) { out.set(a, o); o += a.length; }
    return out;
  }

  async function digest(alg, data) { return new Uint8Array(await subtle.digest(alg, data)); }

  async function aesKey(raw) { return subtle.importKey('raw', raw, { name: 'AES-CBC' }, false, ['encrypt']); }

  // AES-CBC with PKCS#7 padding (as PDF wants for strings and streams)
  async function cbcPad(key, iv, data) {
    return new Uint8Array(await subtle.encrypt({ name: 'AES-CBC', iv: iv }, key, data));
  }

  // AES-CBC with no padding (input is a multiple of 16): drop WebCrypto's extra padding block
  async function cbcNoPad(rawKey, iv, data) {
    const out = await cbcPad(await aesKey(rawKey), iv, data);
    return out.slice(0, data.length);
  }

  // ISO 32000-2 Algorithm 2.B (same as qpdf / pypdf)
  async function hash2B(pwd, salt, udata) {
    let k = await digest('SHA-256', cat(pwd, salt, udata));
    let count = 0;
    for (;;) {
      count++;
      const k1 = cat(pwd, k, udata);
      const rep = new Uint8Array(k1.length * 64);
      for (let i = 0; i < 64; i++) rep.set(k1, i * k1.length);
      const e = await cbcNoPad(k.slice(0, 16), k.slice(16, 32), rep);
      let sum = 0;
      for (let i = 0; i < 16; i++) sum += e[i];
      k = await digest(['SHA-256', 'SHA-384', 'SHA-512'][sum % 3], e);
      if (count >= 64 && e[e.length - 1] <= count - 32) break;
    }
    return k.slice(0, 32);
  }

  const enc = s => new TextEncoder().encode(s).slice(0, 127);

  // Print, copy and text extraction allowed; editing not allowed.
  function permissionsValue() {
    const allowed = (1 << 2) | (1 << 4) | (1 << 9) | (1 << 11); // bits 3, 5, 10, 12
    const reserved = (1 << 6) | (1 << 7);                        // bits 7, 8 must be 1
    return ((0xFFFFF000 | allowed | reserved) >> 0);              // signed 32-bit
  }

  async function buildEncryption(userPassword) {
    const fileKey = rand(32);
    const up = enc(userPassword);
    const op = enc(Array.from(rand(16), b => b.toString(16).padStart(2, '0')).join(''));
    const zeroIv = new Uint8Array(16);

    const uvs = rand(8), uks = rand(8);
    const U = cat(await hash2B(up, uvs, new Uint8Array(0)), uvs, uks);
    const UE = await cbcNoPad(await hash2B(up, uks, new Uint8Array(0)), zeroIv, fileKey);

    const ovs = rand(8), oks = rand(8);
    const O = cat(await hash2B(op, ovs, U), ovs, oks);
    const OE = await cbcNoPad(await hash2B(op, oks, U), zeroIv, fileKey);

    const P = permissionsValue();
    const perms = new Uint8Array(16);
    perms[0] = P & 0xff; perms[1] = (P >>> 8) & 0xff; perms[2] = (P >>> 16) & 0xff; perms[3] = (P >>> 24) & 0xff;
    perms[4] = perms[5] = perms[6] = perms[7] = 0xff;
    perms[8] = 0x54; perms[9] = 0x61; perms[10] = 0x64; perms[11] = 0x62; // 'T' 'a' 'd' 'b'
    perms.set(rand(4), 12);
    const Perms = await cbcNoPad(fileKey, zeroIv, perms); // one block = ECB

    return { fileKey, U, UE, O, OE, P, Perms };
  }

  async function lock(pdfBytes, userPassword) {
    if (!subtle) throw new Error('secure context required');
    const L = root.PDFLib;
    const doc = await L.PDFDocument.load(pdfBytes, { updateMetadata: false });
    const ctx = doc.context;
    if (ctx.trailerInfo.Encrypt) throw new Error('already locked');

    const e = await buildEncryption(userPassword);
    const key = await aesKey(e.fileKey);
    const seal = async bytes => { const iv = rand(16); return cat(iv, await cbcPad(key, iv, bytes)); };

    // Strings anywhere inside an object are replaced by encrypted hex strings.
    async function walk(obj) {
      if (obj instanceof L.PDFString || obj instanceof L.PDFHexString) {
        return L.PDFHexString.of(toHex(await seal(obj.asBytes())));
      }
      if (obj instanceof L.PDFArray) {
        for (let i = 0; i < obj.size(); i++) obj.set(i, await walk(obj.get(i)));
        return obj;
      }
      if (obj instanceof L.PDFDict) {
        for (const [k, v] of obj.entries()) obj.set(k, await walk(v));
        return obj;
      }
      return obj;
    }

    for (const [ref, obj] of ctx.enumerateIndirectObjects()) {
      if (obj instanceof L.PDFRawStream) {
        await walk(obj.dict);
        const sealed = await seal(obj.getContents());
        ctx.assign(ref, L.PDFRawStream.of(obj.dict, sealed));
      } else if (obj instanceof L.PDFStream) {
        // Streams pdf-lib created itself (not expected on load): flatten first
        const raw = obj.getContents();
        await walk(obj.dict);
        ctx.assign(ref, L.PDFRawStream.of(obj.dict, await seal(raw)));
      } else {
        await walk(obj);
      }
    }

    const hex = b => L.PDFHexString.of(toHex(b));
    const cf = ctx.obj({ StdCF: ctx.obj({ AuthEvent: L.PDFName.of('DocOpen'), CFM: L.PDFName.of('AESV3'), Length: 32 }) });
    const encDict = ctx.obj({
      Filter: L.PDFName.of('Standard'), V: 5, R: 6, Length: 256,
      CF: cf, StmF: L.PDFName.of('StdCF'), StrF: L.PDFName.of('StdCF'),
      O: hex(e.O), U: hex(e.U), OE: hex(e.OE), UE: hex(e.UE),
      P: e.P, Perms: hex(e.Perms), EncryptMetadata: true
    });
    ctx.trailerInfo.Encrypt = ctx.register(encDict);
    const id = hex(rand(16));
    ctx.trailerInfo.ID = ctx.obj([id, id]);

    // Classic xref table, no object streams (encrypted object streams are avoided on purpose)
    return doc.save({ useObjectStreams: false, addDefaultPage: false, updateFieldAppearances: false });
  }

  function toHex(b) { let s = ''; for (let i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, '0'); return s; }

  root.PdfLock = { lock: lock };
})(typeof window !== 'undefined' ? window : globalThis);
