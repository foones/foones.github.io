#!/usr/bin/env python
# coding:utf-8:
import os
import sys

PAGES = [
    ('Research', 'research'),
    ('Teaching', 'teaching'),
    ('Misc', 'misc'),
    ('Contact', 'contact'),
]

def menu_static():
    html = []
    for title, page in PAGES:
        html.append(
          '<a href="{page}.html">{title}</a>'.format(
            title=title,
            page=page,
          )
        )
    return ''.join(html)

def generate_static(title, page):
    print('{title} ({page})'.format(title=title, page=page))

    f = open('template.html', 'r')
    html = f.read()
    f.close()

    content = open('{page}.html'.format(page=page), 'r').read()

    html = html.replace('$SCRIPT$', '')
    html = html.replace('$ONLOAD$', '')
    html = html.replace('$MENU$', menu_static())
    html = html.replace('$CONTENT$', content)

    filename = '../{page}.html'.format(page=page)
    f = open(filename, 'w')
    f.write(html)
    f.close()

def menu_dynamic():
    html = []
    for title, page in PAGES:
        html.append(
          '<a href="javascript:show(\'{page}\')">{title}</a>'.format(
            title=title,
            page=page,
          )
        )
    return ''.join(html)

def generate_dynamic(pages):
    print('Dynamic page -- index.html')
    f = open('template.html', 'r')
    html = f.read()
    f.close()

    pp = ', '.join(['"{page}"'.format(page=page) for (title, page) in pages])
    script = [
      '<script type="text/javascript">',
      'function show(id) {',
      '  var pages = [' + pp + '];',
      '  for (var i in pages) {',
      '    var p = pages[i];',
      '    if (p === id) {',
      '      document.getElementById(p).style.display = "block";',
      '    } else {',
      '      document.getElementById(p).style.display = "none";',
      '    }',
      '  }',
      '}',
      '</script>',
    ]

    content = []
    for title, page in pages:
        print('Reading {page}'.format(page=page))
        content.append('<div id="%s">' % (page,))
        content.append(open('{page}.html'.format(page=page), 'r').read())
        content.append('</div>')

    html = html.replace('$SCRIPT$', '\n'.join(script))
    html = html.replace('$ONLOAD$', "show('{page}')".format(page=pages[0][1]))
    html = html.replace('$MENU$', menu_dynamic())
    html = html.replace('$CONTENT$', '\n'.join(content))

    filename = '../index.html'.format(page=page)
    f = open(filename, 'w')
    f.write(html)
    f.close()

if __name__ == '__main__':
    if sys.argv[1:] == ["--statict"]:
        for title, page in PAGES:
            generate_static(title, page)
    else:
        generate_dynamic(PAGES)

