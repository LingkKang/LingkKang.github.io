var hljs = require('highlightjs');
var leanHljs = require('highlightjs-lean');

hljs.registerLanguage("lean", leanHljs);
hljs.initHighlightingOnLoad();
