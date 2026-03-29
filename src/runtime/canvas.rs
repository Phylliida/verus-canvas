#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeCanvas — verified RGBA8 pixel buffer
//  ---------------------------------------------------------------------------

pub struct RuntimeCanvas {
    pub width: usize,
    pub height: usize,
    pub pixels: Vec<u8>,
}

impl RuntimeCanvas {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.width > 0
        &&& self.height > 0
        &&& self.width * self.height * 4 <= usize::MAX
        &&& self.pixels.len() == self.width * self.height * 4
    }

    ///  Pixel buffer index for (x, y).
    pub open spec fn pixel_idx(&self, x: usize, y: usize) -> int {
        (y * self.width + x) * 4
    }

    ///  Create a new canvas filled with transparent black.
    pub fn new(width: usize, height: usize) -> (out: Self)
        requires
            width > 0,
            height > 0,
            width * height * 4 <= usize::MAX,
        ensures
            out.wf_spec(),
            out.width == width,
            out.height == height,
    {
        let total = width * height * 4;
        let mut pixels: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < total
            invariant
                0 <= i <= total,
                pixels.len() == i as int,
                total == width * height * 4,
                total <= usize::MAX,
            decreases total - i,
        {
            pixels.push(0u8);
            i = i + 1;
        }
        RuntimeCanvas { width, height, pixels }
    }

    ///  Read pixel at (x, y) as (r, g, b, a).
    pub fn get_pixel(&self, x: usize, y: usize) -> (out: (u8, u8, u8, u8))
        requires
            self.wf_spec(),
            x < self.width,
            y < self.height,
    {
        let idx = self.pixel_offset(x, y);
        (self.pixels[idx], self.pixels[idx + 1],
         self.pixels[idx + 2], self.pixels[idx + 3])
    }

    ///  Write pixel at (x, y).
    pub fn set_pixel(&mut self, x: usize, y: usize, r: u8, g: u8, b: u8, a: u8)
        requires
            old(self).wf_spec(),
            x < old(self).width,
            y < old(self).height,
        ensures
            self.wf_spec(),
            self.width == old(self).width,
            self.height == old(self).height,
            self.pixels.len() == old(self).pixels.len(),
    {
        let idx = self.pixel_offset(x, y);
        self.pixels.set(idx, r);
        self.pixels.set(idx + 1, g);
        self.pixels.set(idx + 2, b);
        self.pixels.set(idx + 3, a);
    }

    ///  Canvas width accessor.
    pub fn get_width(&self) -> (out: usize)
        requires self.wf_spec(),
        ensures out == self.width,
    {
        self.width
    }

    ///  Canvas height accessor.
    pub fn get_height(&self) -> (out: usize)
        requires self.wf_spec(),
        ensures out == self.height,
    {
        self.height
    }

    ///  Compute and verify the pixel buffer index for (x, y).
    fn pixel_offset(&self, x: usize, y: usize) -> (out: usize)
        requires
            self.wf_spec(),
            x < self.width,
            y < self.height,
        ensures
            out as int == self.pixel_idx(x, y),
            out + 3 < self.pixels.len(),
    {
        proof {
            assert(y * self.width + x < self.height * self.width)
                by (nonlinear_arith)
                requires y < self.height, x < self.width, self.width > 0;
            assert((y * self.width + x) * 4 + 3 < self.height * self.width * 4)
                by (nonlinear_arith)
                requires y * self.width + x < self.height * self.width;
        }
        (y * self.width + x) * 4
    }
}

} //  verus!
