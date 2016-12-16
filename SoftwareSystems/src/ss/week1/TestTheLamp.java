package ss.week1;

public class TestTheLamp {
	
	public static void main(String[] args) {
		ThreeWayLamp test = new ThreeWayLamp();
		System.out.println("Initialized the lamp, with value:");
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println(test.getSetting());
		test.switchSetting();
		System.out.println("After fourth increment, should return to zero:");
		System.out.println(test.getSetting());
		test.switchSetting();
	}
	
}
