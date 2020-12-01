import java.util.Arrays;
import java.util.Comparator;

public class Fruit implements Comparable<Fruit> {
	private String name;
	private int price;

	public Fruit(String name, int price) {
		this.name = name;
		this.price = price;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public int getPrice() {
		return price;
	}

	public void setPrice(int price) {
		this.price = price;
	}

	@Override
	public int compareTo(Fruit compareFruit) {
		int comparePrice = compareFruit.getPrice();

		// ascending order
		return this.price - comparePrice;

		// descending order
		//return comparePrice - this.price;
	}


	public static void main(String[] args) {
		Fruit[] fruits = new Fruit[4];
		fruits[0] = new Fruit("Pineapple", 70);
		fruits[1] = new Fruit("Apple", 30);
		fruits[2] = new Fruit("Orange", 35);
		fruits[3] = new Fruit("Banana", 50);

		System.out.println("Sort by name");
		Arrays.sort(fruits);

		for (Fruit fruit : fruits) {
			System.out.print(fruit.getName() + " ");
		}


		System.out.println("\n\nSort by price");
		Arrays.sort(fruits, new Comparator<Fruit>() {
			@Override
			public int compare(Fruit left, Fruit right) {
				return left.getPrice() - right.getPrice();
			}
		});

		for (Fruit fruit : fruits) {
			System.out.print(fruit.getName() + "(" + fruit.getPrice() + ") ");
		}
	}
}
