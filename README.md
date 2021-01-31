# Tarea3VFLuisBLluis
## Autor: Luis Felipe Benítez Lluis LL11
Repositorio con los archivos de coq correspondientes a la tarea 3 del curso de Verificación Formal 2021-1
## Arquitectura
Este repositorio manejó las dependencias de los archivos mediante los comandos *Add LoadPath <_path_>* y *Load <archivo>* en lugar de la 
forma anterior mediante un archivo *_CoqProject*.
No obstante, en la carpeta "ProjectCoq" se encuentran dos versiones de un archivo *_CoqProject* por si hay problemas de portabilidad. Para cargar adecuadamente los archivos quizás se requiera alterar cada script a que tenga la línea  
*Add LoadPath <inserte aquí la dirección de sus archivos>* al comienzo. En mi versión de coq y en mi equipo las cargas y ejecuciones fueron exitosas.

El siguiente proyecto contiene los siguientes archivos. 
1. *Defs_BN.v*: Definiciones de
    *bn sucBN predBN toN toBN plusBN* y 
    *ltBN lteqBN*. Este archivo corresponde con 
    *bn2.v* y *orderbn.v*. No posee dependencias.
2. *Defs_BT.v*: Definiciones de
    *BTree, bsize, bbal lookup_bn, update,
    le, he*. Este archivo corresponde con los
    archivos *binary_tree.v , braunT_bn.v, 
    lookupdBN, btExtensions*. Este archivo
    depende *Defs_BN.v".
3. *Props_BN.v*: Teoremas de números por paridad.
     Este archivo corresponde con 
    *bn2.v* y *orderbn.v*. Depende de *Defs_BT.v*.Este archivo
    depende *Defs_BT.v".
4. *Props_BT.v*: Propiedades árboles de Braun y 
    ejercicios de tarea3
    Este archivo corresponde con los
    archivos *binary_tree.v , braunT_bn.v, 
    lookupdBN, btExtensions*. Este archivo
    depende *Props_BT.v".
	
## Dependencias
Las dependencias de estos archivos están en el orden mencionado anteriormente. 

## Nota
Las definiciones de *lr hr* se encuentran en el 
archivo *Props_BT.v* para dar conexidad a los ejercicios. Los ejercicios se pueden encontrar rápidamente buscando la cadena "123". 

En el archivo *Props_BN.v hay unas cuantas propiedades de orden admitidas pues se comentó que no era absolutamente necesario probar todo 
para esta tarea. En el archivo *Props_BT.v*
Hay un teorema admitido que solo es usado en dos lemas que no figuran en los ejercios por lo que se tienen comentados. Se pueden hallar rápidamente buscando la cadena "456". 