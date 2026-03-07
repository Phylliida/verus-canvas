// ---------------------------------------------------------------------------
// RuntimeCanvas — RGBA8 pixel buffer (trusted exec, not verified)
// ---------------------------------------------------------------------------

/// A simple RGBA8 pixel buffer.
pub struct RuntimeCanvas {
    width: usize,
    height: usize,
    pixels: Vec<u8>,
}

impl RuntimeCanvas {
    /// Create a new canvas filled with transparent black (all zeros).
    pub fn new(width: usize, height: usize) -> Self {
        RuntimeCanvas {
            width,
            height,
            pixels: vec![0u8; width * height * 4],
        }
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn pixels(&self) -> &[u8] {
        &self.pixels
    }

    /// Get the RGBA values at (x, y).
    pub fn get_pixel(&self, x: usize, y: usize) -> [u8; 4] {
        let idx = (y * self.width + x) * 4;
        [
            self.pixels[idx],
            self.pixels[idx + 1],
            self.pixels[idx + 2],
            self.pixels[idx + 3],
        ]
    }

    /// Set the RGBA values at (x, y).
    pub fn set_pixel(&mut self, x: usize, y: usize, rgba: [u8; 4]) {
        let idx = (y * self.width + x) * 4;
        self.pixels[idx]     = rgba[0];
        self.pixels[idx + 1] = rgba[1];
        self.pixels[idx + 2] = rgba[2];
        self.pixels[idx + 3] = rgba[3];
    }

    /// Source-over composite a single pixel (approximate u8 arithmetic).
    pub fn blend_pixel_over(&mut self, x: usize, y: usize, src: [u8; 4]) {
        let sa = src[3] as u16;
        if sa == 0 {
            return; // fully transparent source, no-op
        }
        if sa == 255 {
            self.set_pixel(x, y, src);
            return; // fully opaque source, overwrite
        }
        let dst = self.get_pixel(x, y);
        let inv_sa = 255 - sa;
        // Premultiplied alpha source-over: out_c = src_c + dst_c * (1 - src_a)
        let out_r = (src[0] as u16 + (dst[0] as u16 * inv_sa + 127) / 255) as u8;
        let out_g = (src[1] as u16 + (dst[1] as u16 * inv_sa + 127) / 255) as u8;
        let out_b = (src[2] as u16 + (dst[2] as u16 * inv_sa + 127) / 255) as u8;
        let out_a = (sa           + (dst[3] as u16 * inv_sa + 127) / 255) as u8;
        self.set_pixel(x, y, [out_r, out_g, out_b, out_a]);
    }

    /// Fill entire canvas with a single color.
    pub fn clear(&mut self, color: [u8; 4]) {
        for i in 0..self.pixels.len() / 4 {
            let idx = i * 4;
            self.pixels[idx]     = color[0];
            self.pixels[idx + 1] = color[1];
            self.pixels[idx + 2] = color[2];
            self.pixels[idx + 3] = color[3];
        }
    }
}
