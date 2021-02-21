
import java.util.Scanner;

import javax.lang.model.util.ElementScanner6;

import java.util.ArrayList;
import java.util.Objects;
import java.lang.Math;

public class Complex
{
    public double re, im;

    public Complex(double real, double imag)
    {
        re = real;
        im = imag;
    }

    public String toString()
    {
        if(im == 0)
        {
            return re + "";
        }
        else if(re == 0)
        {
            return im + "i";
        }
        else
        {
            return re + " + "  + im + "i";
        }
    }

    public double abs()
    {
        return Math.hypot(re, im);
    }

    public double phase()
    {
        return Math.atan2(im, re);
    }

    public double add(Complex z)
    {
        return new Complex(re + z.re, im + z.im);
    }

    public double sub(Complex z)
    {
        return new Complex(re - z.re, im - z.im);
    }

    public Complex mul(Complex z)
    {
        return new Complex(re * z.re - im * z.im, re * z.im + im * z.re);
    }
    public Complex mul(double z)
    {
        return new Complex(re * z, im * z);
    }

    public Complex inverse()
    {
        double c = re * re + im * im;
        return new Complex(re / c, -im / c);
    }

    public Complex div(Complex z)
    {
        double c = z.re * z.re + z.im * z.im;
        return new Complex((re * z.re + im * z.im) / c, (-re * z.im + im * z.re) / c);
    }
    public Complex div(double z)
    {
        return new Complex(re / z, im / z);
    }

    public Complex exp()
    {
        double c = Math.exp(re);
        return new Complex(c * Math.cos(im), c * Math.sin(im));
    }

    public Complex sin()
    {
        return new Complex(Math.sin(re) * Math.cosh(im), Math.cos(re) * Math.sinh(im));
    }
    public Complex cos()
    {
        return new Complex(Math.cos(re) * math.cosh(im), -Math.sin(re) * Math.sinh(im));
    }
    public Complex tan()
    {
        return sin().div(cos());
    }

}