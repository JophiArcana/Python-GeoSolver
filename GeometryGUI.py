
import tkinter as tk, FundamentalsAlter
from tkinter import *
from FundamentalsAlter import *

break_symbols = ['(', ')', ',', '.', '=']

def try_eval(s):
    try:
        return eval(s)
    except:
        pass

###############################
     # String Evaluation #
###############################

def splice(s):
    if not s:
        return []
    elif s[0] == ' ':
        return splice(s[1:])
    elif len(s) == 1:
        return [s[0]]
    elif s[0] in break_symbols or s[1] in break_symbols:
        return [s[0]] + splice(s[1:])
    else:
        sp = splice(s[1:])
        return ([s[0]] + sp) if sp[0] in break_symbols else ([s[0] + sp[0]] + sp[1:])

def parse(s):
    k = splice(s)
    def f(s):
        directory = lambda l: [i for i, j in inspect.getmembers(l)]
        if s in break_symbols or (s in directory(FundamentalsAlter) and s != 'i') or s in directory(__builtins__) or s == 'name' or type(try_eval(s)) in [int, float, complex, str]:
            return s
        else:
            return f'self.{s}'
    return ''.join(map(f, k))

################################
     # Construction Class #
################################

class Construction(Tk):
    def __init__(self, width = 800, height = 600, diagram = dict(), default_scale = 30):
        Tk.__init__(self)
        self.title('Geometry Alter')
        self.canvas = tk.Canvas(self, width = width, height = height, bg = 'white')
        self.canvas.pack()
        self.update_idletasks()
        self.default_scale = default_scale
        self.scale, self.width, self.height = 1, self.canvas.winfo_reqwidth(), self.canvas.winfo_reqheight()
        self.entry = tk.Entry(self)
        if self.width > self.height:
            self.canvas.create_window((self.width - self.height) / 2, self.height / 2, window = self.entry)
        else:
            self.canvas.create_window(self.width / 2, (self.width + self.height) / 2, window = self.entry)

        self.canvas.bind("<Button-1>", self.on_drag_start)
        self.canvas.bind("<B1-Motion>", self.on_drag_motion)


        self.quit_button = Button(self, text = 'Quit', command = self.quit)
        self.quit_button.pack()
        self.reset_button = Button(self, text = 'Reset Scale', command = self.reset_scale)
        self.reset_button.pack()

        self.original_directory = dir(self) + ['original_directory']

        self.__dict__.update(diagram)

        self.bind('<Return>', self.read)
        self.bind('<MouseWheel>', self.scroll)
        
        self.update_diagram()

    def update_diagram(self):
        self.canvas.config(width = self.winfo_width() - 4, height = self.winfo_height() - 56, bg = 'white')
        self.width, self.height = self.winfo_width() - 4, self.winfo_height() - 56
        for v in self.__dict__.values():
            if isinstance(v, Base):
                self.update_obj(v)
        self.after(2, self.update_diagram)

    def on_drag_start(self, event):
        self.canvas.selected = None
        r = 2 * self.scale / self.default_scale
        z = complex(*self.reverse(x = event.x, y = event.y))
        for v in list(vars(self).values())[15:]:
            if isinstance(v, Phantom) and v.degrees >= 2 and abs(v.z - z) < r:
                self.canvas.selected = v
                break
        if self.canvas.selected:
            self.canvas._drag_start_x = event.x
            self.canvas._drag_start_y = event.y 

    def on_drag_motion(self, event):
        if self.canvas.selected:
            self.canvas.selected.inputs[0] = complex(*self.reverse(x = event.x, y = event.y))

    def transform(self, **kwargs):
        if 'x' in kwargs:
            kwargs['x'] = kwargs['x'] * self.default_scale * self.scale + self.width / 2
        if 'y' in kwargs:
            kwargs['y'] = kwargs['y'] * -self.default_scale * self.scale + self.height / 2
        if 'r' in kwargs:
            kwargs['r'] = kwargs['r'] * self.default_scale * self.scale
        return tuple(kwargs.values())

    def reverse(self, **kwargs):
        if 'x' in kwargs:
            kwargs['x'] = (kwargs['x'] - self.width / 2) / (self.default_scale * self.scale)
        if 'y' in kwargs:
            kwargs['y'] = (kwargs['y'] - self.height / 2) / (-self.default_scale * self.scale)
        if 'r' in kwargs:
            kwargs['r'] = kwargs['r'] / (self.default_scale * self.scale)
        return tuple(kwargs.values())

    def get_coords(self, p):
        assert any(isinstance(p, t) for t in trinity)
        if isinstance(p, Phantom):
            x, y = self.transform(x = p[0], y = p[1])
            return (x - 2, y - 2, x + 2, y + 2)
        elif isinstance(p, Linear):
            z, a = p.z, p.angle
            if a > 0:
                intersect_left = [intersect(z, -self.width / (60 * self.scale), a, pi / 2), intersect(z, -self.height * i / (60 * self.scale), a, 0)]
                intersect_right = [intersect(z, self.width / (60 * self.scale), a, pi / 2), intersect(z, self.height * i / (60 * self.scale), a, 0)]
            else:
                intersect_left = [intersect(z, -self.width / (60 * self.scale), a, pi / 2), intersect(z, self.height * i / (60 * self.scale), a, 0)]
                intersect_right = [intersect(z, self.width / (60 * self.scale), a, pi / 2), intersect(z, -self.height * i / (60 * self.scale), a, 0)]
            z1 = list(filter(lambda k: abs(re(k)) <= self.width / (57 * self.scale) and abs(im(k)) <= self.height / (57 * self.scale), intersect_left))[0]
            z2 = list(filter(lambda k: abs(re(k)) <= self.width / (57 * self.scale) and abs(im(k)) <= self.height / (57 * self.scale), intersect_right))[0]
            return (*self.transform(x = re(z1), y = im(z1)), *self.transform(x = re(z2), y = im(z2)))
        elif isinstance(p, Circle):
            x, y, r = self.transform(x = re(p.z), y = im(p.z), r = p.radius)
            return (x - r, y - r, x + r, y + r)

    def format(self, p):
        assert any(isinstance(p, t) for t in trinity)
        if isinstance(p, Phantom):
            return self.canvas.create_oval(*self.get_coords(p), fill = 'black')
        elif isinstance(p, Linear):
            return self.canvas.create_line(*self.get_coords(p))
        elif isinstance(p, Circle):
            return self.canvas.create_oval(*self.get_coords(p))

    def update_obj(self, p):
        if not hasattr(p, 'index'):
            setattr(p, 'index', self.format(p))
        else:
            self.canvas.coords(p.index, self.get_coords(p))

    def read(self, event):
        if (s := self.entry.get()):
            directory = lambda l: [i for i, j in inspect.getmembers(l)]
            if any(term in (self.original_directory + directory(FundamentalsAlter) + directory(__builtins__)) for term in s):
                pass
            else:
                exec(parse(s))
            v = list(vars(self).values())[-1]
            if not hasattr(v, 'index'):
                setattr(v, 'index', self.format(v))
        self.entry.delete(0, END)

    def scroll(self, event):
        self.scale = min(max(0.5, self.scale + 0.1 * (event.delta / 120)), 3)

    def quit(self):
        self.after(500, self.destroy())

    def reset_scale(self):
        self.scale = 1

p, q, r = Phantom(4, name = 'p'), Phantom(4 * cis(2 * pi / 3), name = 'q'), Phantom(4 * cis(4 * pi / 3), name = 'r')
example = {'p': p, 'q': q, 'r': r}
example['l'], example['m'], example['n'] = Connect(q, r, name = 'l'), Connect(r, p, name = 'm'), Connect(p, q, name = 'n')
example['c'], example['i'] = Circumcircle(p, q, r, name = 'c'), Incircle(p, q, r, name = 'i')
example['exp'], example['exq'], example['exr'] = Excircle(p, q, r, name = 'exp'), Excircle(q, r, p, name = 'exq'), Excircle(r, p, q, name = 'exr')

width = float(input('Input width: ').strip())
height = float(input('Input height: ').strip())

construct = Construction(width = width, height = height, diagram = example)
construct.mainloop()
