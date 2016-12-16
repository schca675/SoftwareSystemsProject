package ss.week2;

public class ThreeWayLamp {
	private int currentSetting;
	public static final int OFF = 0;
	public static final int LOW = 1;
	public static final int MEDIUM = 2;
	public static final int HIGH = 3;

	//@ private invariant currentSetting>=OFF && currentSetting<=HIGH;

	//@ ensures getSetting() == OFF;
	public ThreeWayLamp() { 
		currentSetting = OFF;
		assert currentSetting == OFF;
	}

	//@ ensures \result >=OFF && \result <=HIGH;
	/*@ pure */ public int getSetting() {
		assert currentSetting <= HIGH && currentSetting >= OFF;
		return currentSetting;
	}

	//@ ensures getSetting()==(\old(getSetting()) + 1) % 4;
	public void switchSetting() {
		int oldSetting = currentSetting;
		assert currentSetting <= HIGH && currentSetting >= OFF;
		currentSetting = (currentSetting + 1) % 4;
		assert currentSetting <= HIGH && currentSetting >= OFF;
		assert currentSetting == (oldSetting + 1) % 4;
	}

}
