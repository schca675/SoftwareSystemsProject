package model;

public class CoordinatesOutOfBoundsException extends DummyException {
	private static final long serialVersionUID = 1L;
	private int x;
	private int y;
	private int z = -1;
	private int xDim;
	private int yDim;
	private int zDim;
	
	public CoordinatesOutOfBoundsException(int x, int y, Board board) {
		this.x = x;
		this.y = y;
		this.xDim = board.xDim;
		this.yDim = board.yDim;
	}
	
	public CoordinatesOutOfBoundsException(int x, int y, int z, Board board) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.xDim = board.xDim;
		this.yDim = board.yDim;
		this.zDim = board.zDim;
	}
	
	@Override
	public String getMessage() {
		if (z == -1) {
			return "Tower coordinates larger than board dimensions. Got (" + x + ", " + y + 
					"), dimensions (" + xDim + ", " + yDim + ").";
		} else if (zDim == Board.UNLIMITED_Z) {
			return "Cell coordinates larger than board dimensions. Got (" + x + ", " + y + ", " + z
					+ "), dimensions (" + xDim + ", " + yDim + ", Inf).";
		} else {
			return "Cell coordinates larger than board dimensions. Got (" + x + ", " + y + ", " + z
					+ "), dimensions (" + xDim + ", " + yDim + ", " + zDim + ").";
		}
	}
}