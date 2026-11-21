use std::path::Path;

fn main() {
    let out_dir = std::env::var("OUT_DIR").unwrap();
    let ico_path = Path::new(&out_dir).join("ggvoice.ico");

    let size = 64u32;
    let mut img = image::RgbaImage::new(size, size);

    let glyph_g: [&str; 9] = [
        ".#####.",
        "##...##",
        "##.....",
        "##.....",
        "##.####",
        "##...##",
        "##...##",
        "##...##",
        ".#####.",
    ];

    for y in 0..size {
        for x in 0..size {
            let is_outer_border = x < 2 || x >= size - 2 || y < 2 || y >= size - 2;
            let px = if is_outer_border {
                image::Rgba([244, 42, 133, 255])
            } else {
                image::Rgba([10, 10, 14, 255])
            };
            img.put_pixel(x, y, px);
        }
    }

    let mut draw_g = |start_x: u32, start_y: u32, color: [u8; 3]| {
        let scale = 3u32;
        for (row, line) in glyph_g.iter().enumerate() {
            for (col, ch) in line.chars().enumerate() {
                if ch == '#' {
                    for sy in 0..scale {
                        for sx in 0..scale {
                            let px = start_x + (col as u32) * scale + sx;
                            let py = start_y + (row as u32) * scale + sy;
                            if px < size && py < size {
                                img.put_pixel(px, py, image::Rgba([color[0], color[1], color[2], 255]));
                            }
                        }
                    }
                }
            }
        }
    };

    // Левая G (белая с неоново-розовой тенью)
    draw_g(10, 19, [244, 42, 133]);
    draw_g(8, 18, [240, 240, 245]);

    // Правая G (неоново-розовая с тёмной тенью)
    draw_g(36, 19, [110, 20, 65]);
    draw_g(34, 18, [244, 42, 133]);

    img.save(&ico_path).expect("Failed to save ggvoice.ico");

    let mut res = winresource::WindowsResource::new();
    res.set_icon(ico_path.to_str().unwrap());
    res.set_manifest(
        r#"
<assembly xmlns="urn:schemas-microsoft-com:asm.v1" manifestVersion="1.0">
<trustInfo xmlns="urn:schemas-microsoft-com:asm.v3">
    <security>
        <requestedPrivileges>
            <requestedExecutionLevel level="requireAdministrator" uiAccess="false" />
        </requestedPrivileges>
    </security>
</trustInfo>
</assembly>
"#,
    );
    res.compile().unwrap();
}