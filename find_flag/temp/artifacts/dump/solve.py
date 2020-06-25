import json
from PIL import Image, ImageDraw

winner = None
with open("room/rWinner.json", "r") as f:
    winner = json.load(f)

w = 3200
h = 608
tiles = winner["tiles"]

im = Image.new('RGB', (w, h), (0, 0, 0))
draw = ImageDraw.Draw(im)
for tile in tiles:
    pos = tile["pos"]
    x, y = pos["x"], pos["y"]
    print(x, y)
    size = tile["size"]
    w, h = size["width"], size["height"]
    x2, y2 = x+w, y + h
    draw.rectangle([(x, y), (x2, y2)], fill=(255, 255, 255))

im.show()