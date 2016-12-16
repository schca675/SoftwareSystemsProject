package ss.week2;

public class Rectangle {
	private int length;
	private int width;

	//@ private invariant length >= 0;
	//@ private invariant width >= 0;

	/**
	 * Create a new Rectangle with the specified length and width.
	 */
	/*@ requires theLength >= 0 && theWidth >= 0; 
	  ensures length() == theLength; 
	  ensures width() == theWidth;
	 */
	public Rectangle(int theLength, int theWidth) {
		assert theLength >= 0 && theWidth >= 0;
		length = theLength;
		width = theWidth;
		assert this.length() == theLength && this.width() == theWidth;
		assert length >= 0 && width >= 0;
	}

	/**
	 * The length of this Rectangle.
	 */
	//@ ensures \result >= 0;
	/*@ pure */ public int length() {
		assert length >= 0;
		return length;
	}

	/**
	 * The width of this Rectangle.
	 */
	//@ ensures \result >=0;
	/*@ pure */ public int width() {
		assert width >= 0;
		return width;
	}

	/**
	 * The area of this Rectangle.
	 */
	//@ ensures \result >=0;
	//@ ensures \result == length() * width();
	//@pure;
	    public int area() {
		assert length >= 0 && width >= 0;
		int calcArea = width * length;
		assert calcArea >= 0;
		assert calcArea == this.length() * this.width();
		return calcArea;
	}

	/**
	 * The perimeter of this Rectangle.
	 */
	//@ ensures \result >=0;
	//@ ensures \result == 2*length()+2*width();
	/*@ pure */ public int perimeter() {
		assert length >= 0 && width >= 0;
		int calcPer = 2 * (length + width);
		assert calcPer >= 0;
		assert calcPer == 2*(this.length() + this.width());
		return calcPer;
	}
}
