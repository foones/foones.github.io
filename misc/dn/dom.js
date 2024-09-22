
// DOM

function clearElem(elem) {
  while (elem.firstChild) {
    elem.removeChild(elem.firstChild);
  }
}

function BUTTON(text, action) {
  let elem = document.createElement('input');
  elem.type = 'button';
  elem.value = text;
  elem.onclick = action;
  return elem;
}

function DIV(cls, children) {
  let elem = document.createElement('div');
  elem.className = cls;
  for (let child of children) {
    elem.appendChild(child);
  }
  return elem;
}

function INPUT_TEXT(value) {
  let elem = document.createElement('input');
  elem.type = 'text';
  elem.value = value;
  elem.onfocus = function () {
    elem.select();
  };
  elem.oninput = function () {
    this.style.width = this.value.length + "ch";
  };
  elem.oninput();
  return elem;
}

function P(child) {
  let elem = document.createElement('p');
  elem.appendChild(child);
  return elem;
}

function TEXT(str) {
  return document.createTextNode(str);
}

